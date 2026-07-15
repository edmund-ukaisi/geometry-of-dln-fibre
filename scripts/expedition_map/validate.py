"""The validator: contracts 1-10 from docs/policies/expedition-map.md.

Findings carry a level (``error`` | ``warning``), the contract number, the node
id (if any), and a message. Errors fail the command (exit nonzero); warnings do
not, unless ``--strict``. ``--fast`` runs the structural contracts only (1, 2
structural, 6, 7, 8, 9, 10) and skips the survey-heavy ones (3, 4, 5); it uses
survey data for existence only when a survey happens to be present.

Design note where the spec leaves room: several checks that the spec frames as
hard contracts (2 existence, 9 route-adoption) can only be *definitively*
enforced against a full-mode survey or a live Lean elaboration. In v0, against a
cone-mode survey or with no survey, those degrade to warnings rather than false
errors -- the map stays honest without blocking on data it cannot see. See
docs/policies/expedition-cli-notes.md.
"""

from __future__ import annotations

from . import model


class Finding:
    __slots__ = ("level", "contract", "node", "message")

    def __init__(self, level, contract, node, message):
        self.level = level
        self.contract = contract
        self.node = node
        self.message = message

    def __repr__(self):
        loc = f" [{self.node}]" if self.node else ""
        return f"C{self.contract} {self.level.upper()}{loc}: {self.message}"


def _err(c, node, msg):
    return Finding("error", c, node, msg)


def _warn(c, node, msg):
    return Finding("warning", c, node, msg)


# ---------------------------------------------------------------------------
# Contract 1 -- well-formed DAG, stable ids, exit nodes forward.
# ---------------------------------------------------------------------------

def c1_dag(m, survey, fast):
    out = []
    ids = set(m["by_id"])
    for n in m["nodes"]:
        if n.get("status") not in model.ALL_STATUSES:
            out.append(_err(1, n["id"], f"unknown status {n.get('status')!r}"))
        for e in n["edges"]:
            if e["type"] not in model.ALL_EDGE_TYPES:
                out.append(_err(1, n["id"], f"unknown edge type {e['type']!r}"))
            if e["to"] not in ids:
                out.append(_err(1, n["id"],
                                f"edge {e['type']} -> {e['to']!r}: no such node"))
    cyc = model.find_cycles(model.build_dep_graph(m))
    if cyc:
        out.append(_err(1, None, "dependency cycle: " + " -> ".join(cyc)))
    # Exit-status nodes must carry a forwarding pointer.
    for n in m["nodes"]:
        if model.is_exit(n):
            has_fwd = any(e["type"] in model.EXIT_EDGE_TYPES for e in n["edges"])
            if not has_fwd:
                out.append(_err(1, n["id"],
                                f"status {n['status']} but no forwarded-to/"
                                "superseded-by pointer"))
    return out


# ---------------------------------------------------------------------------
# Contract 2 -- stated+ => lean anchor exists (+ pin elaborates at green-gate).
# ---------------------------------------------------------------------------

def c2_anchors(m, survey, fast):
    out = []
    snodes = survey["nodes"] if survey else {}
    mode = survey["freshness"]["walker_mode"] if survey else None
    for n in m["nodes"]:
        needs_anchor = (n["kind"] == "claim" and model.at_least(n, "stated")) or \
                       (n["kind"] == "route" and model.at_least(n, "adopted"))
        lean = n.get("lean")
        if needs_anchor and not lean:
            out.append(_warn(2, n["id"],
                             f"{n['status']} but no `lean` anchor (add one; "
                             "pin cannot be emitted)"))
        if not lean:
            continue
        s = snodes.get(n["id"])
        if s is None:
            if not fast:
                out.append(_warn(2, n["id"],
                                 "no survey: cannot check anchor existence"))
            continue
        if s["match"] == "none" and s["lean_exists"] is None and mode == "cone":
            out.append(_warn(2, n["id"],
                             f"anchor {lean!r} not in root cone (may be live "
                             "frontier; run full walker to confirm existence)"))
        elif s["lean_exists"] is False:
            out.append(_err(2, n["id"],
                            f"anchor {lean!r} not found in kernel (walker is full)"))
    return out


# ---------------------------------------------------------------------------
# Contract 3 -- computed statuses match kernel (proven <=> sorry-free closure).
# ---------------------------------------------------------------------------

def c3_status_kernel(m, survey, fast):
    out = []
    if fast or not survey:
        return out
    mode = survey["freshness"]["walker_mode"]
    for n in m["nodes"]:
        if n.get("status") != "proven":
            continue
        s = survey["nodes"].get(n["id"], {})
        if mode != "full":
            out.append(_warn(3, n["id"],
                             "status=proven unverifiable (cone-mode survey has "
                             "no axiom data)"))
            continue
        if s.get("lean_exists") is False:
            out.append(_err(3, n["id"], "status=proven but anchor not in kernel"))
        elif s.get("sorry_tainted"):
            cone = s.get("sorry_cone") or []
            out.append(_err(3, n["id"],
                            "status=proven but closure is sorry-tainted: "
                            + ", ".join(model.short_name(c) for c in cone[:4])))
    return out


# ---------------------------------------------------------------------------
# Contract 4 -- discharges edges witnessed once consumer >= skeleton-linked.
# ---------------------------------------------------------------------------

def c4_discharge_witness(m, survey, fast):
    out = []
    if fast or not survey:
        return out
    for n in m["nodes"]:
        for e in n["edges"]:
            if e["type"] != "discharges":
                continue
            consumer = m["by_id"].get(e["to"])
            if consumer is None or not model.at_least(consumer, "skeleton-linked"):
                continue  # not yet in the skeleton; edge not expected to witness
            info = survey["witness"].get(f"{n['id']}->{e['to']}", {})
            if info.get("witnessed") is True:
                continue
            if info.get("witnessed") is False:
                out.append(_err(4, n["id"],
                                f"discharges {e['to']}: UNWITNESSED "
                                f"({info.get('reason')})"))
            else:
                out.append(_warn(4, n["id"],
                                 f"discharges {e['to']}: UNWITNESSED "
                                 f"({info.get('reason', 'no survey dep data')})"))
    return out


# ---------------------------------------------------------------------------
# Contract 5 -- live sorries subset of mapped nodes; fossils flagged.
# ---------------------------------------------------------------------------

def c5_sorry_registered(m, survey, fast):
    out = []
    if fast or not survey:
        return out
    mode = survey["freshness"]["walker_mode"]
    if mode != "full":
        out.append(_warn(5, None,
                         "cone-mode survey: live-sorry cone not computed "
                         "(no dep/axiom data)"))
        return out
    mapped = set()
    for n in m["nodes"]:
        r = survey["nodes"].get(n["id"], {}).get("resolved")
        if r:
            mapped.add(r)
    for d in survey.get("live_sorry", []):
        if d not in mapped:
            out.append(_err(5, None,
                            f"live sorry not on any mapped node: {model.short_name(d)}"))
    return out


# ---------------------------------------------------------------------------
# Contract 6 -- open node has owner or explicit parked.
# ---------------------------------------------------------------------------

def c6_ownership(m, survey, fast):
    out = []
    for n in m["nodes"]:
        if not model.is_open(n):
            continue
        owner = (n.get("owner") or "").strip()
        if not owner:
            out.append(_err(6, n["id"],
                            "open node has no owner (use `owner:` or "
                            "`owner: 'parked: <reason>'`)"))
    return out


# ---------------------------------------------------------------------------
# Contract 7 -- notions consumed by stated+ claims are >= validated.
# ---------------------------------------------------------------------------

def c7_notions(m, survey, fast):
    out = []
    for n in m["nodes"]:
        if n["kind"] != "claim" or not model.at_least(n, "stated"):
            continue
        for e in n["edges"]:
            if e["type"] != "needs":
                continue
            dep = m["by_id"].get(e["to"])
            if dep is None or dep["kind"] != "notion":
                continue
            if not model.at_least(dep, "validated"):
                out.append(_err(7, dep["id"],
                                f"notion consumed by stated+ claim {n['id']} "
                                f"but only {dep['status']} (need >= validated)"))
    return out


# ---------------------------------------------------------------------------
# Contract 8 -- every open node reachable from a root.
# ---------------------------------------------------------------------------

def c8_reachable(m, survey, fast):
    out = []
    roots = m["meta"].get("roots", [])
    if not roots:
        out.append(_err(8, None, "meta.roots is empty; liveness undefined"))
        return out
    for r in roots:
        if r not in m["by_id"]:
            out.append(_err(8, None, f"root {r!r} is not a node"))
    reach = model.reachable_from_roots(m)
    for n in m["nodes"]:
        if model.is_open(n) and n["id"] not in reach:
            out.append(_err(8, n["id"],
                            "open node not reachable from any root "
                            "(orphaned effort / drift)"))
    return out


# ---------------------------------------------------------------------------
# Contract 9 -- route-adoption gate for routes at adopted+.
# ---------------------------------------------------------------------------

def c9_route_gate(m, survey, fast):
    out = []
    for n in m["nodes"]:
        if n["kind"] != "route" or not model.at_least(n, "adopted"):
            continue
        needs = [e["to"] for e in n["edges"] if e["type"] == "needs"]
        if not needs:
            out.append(_warn(9, n["id"],
                             "adopted route has no `needs` edges: nothing to "
                             "compose (adoption gate (a) cannot hold)"))
        for t in needs:
            dep = m["by_id"].get(t)
            if dep and dep["kind"] == "claim" and not model.at_least(dep, "stated"):
                out.append(_warn(9, n["id"],
                                 f"adopted route needs {t} which is only "
                                 f"{dep['status']}: skeleton cannot elaborate "
                                 "against a verbatim statement yet (gate (a))"))
        # Gate (b): some battery must evaluate the route's hypotheses.
        has_batt = bool(n.get("kill")) or any(
            m["by_id"].get(t, {}).get("kill") for t in needs
        )
        if not has_batt:
            out.append(_warn(9, n["id"],
                             "adopted route: no battery evaluates its "
                             "hypotheses (adoption gate (b))"))
    return out


# ---------------------------------------------------------------------------
# Contract 10 -- lints (budgets + selling-register). Warnings only.
# ---------------------------------------------------------------------------

def c10_lints(m, survey, fast):
    out = []
    # notes must be one line.
    for n in m["nodes"]:
        notes = n.get("notes") or ""
        if "\n" in notes.strip():
            out.append(_warn(10, n["id"], "`notes` spans multiple lines (one-line hook only)"))
    # STATUS.md budget.
    status_path = m["map_dir"] / "STATUS.md"
    if status_path.is_file():
        nlines = len(status_path.read_text().splitlines())
        if nlines > 40:
            out.append(_warn(10, None, f"STATUS.md is {nlines} lines (budget <= 40)"))
    # priorities.md budget.
    prio_path = m["map_dir"] / "priorities.md"
    if prio_path.is_file():
        nlines = len(prio_path.read_text().splitlines())
        if nlines > 30:
            out.append(_warn(10, None, f"priorities.md is {nlines} lines (budget <= 30)"))
    # Selling-register lint.
    for n in m["nodes"]:
        if n["kind"] not in ("claim", "route"):
            continue
        text = f"{n.get('title', '')} {n.get('notes', '')}".lower()
        hits = [w for w in model.SELLING_WORDS if w in text]
        has_evidence = bool(n.get("evidence")) or bool(n.get("kill"))
        if hits and not has_evidence:
            out.append(_warn(10, n["id"],
                             f"selling-register word(s) {hits} without an "
                             "evidence/battery pointer (P5)"))
    return out


# ---------------------------------------------------------------------------
# Contract 11 -- landmarks: hard cap <= 9; landmark not on an exit status.
# ---------------------------------------------------------------------------

def c11_landmarks(m, survey, fast):
    out = []
    lms = model.landmarks(m)
    if len(lms) > model.LANDMARK_CAP:
        names = ", ".join(n["id"] for n in lms)
        out.append(_err(11, None,
                        f"{len(lms)} landmarks exceed the cap of "
                        f"{model.LANDMARK_CAP}; demote one. Landmarks: {names}"))
    for n in lms:
        if model.is_exit(n):
            out.append(_warn(11, n["id"],
                             f"stale landmark: status {n['status']} (retire from "
                             "the carried shortlist)"))
    return out


CONTRACTS = [
    c1_dag, c2_anchors, c3_status_kernel, c4_discharge_witness,
    c5_sorry_registered, c6_ownership, c7_notions, c8_reachable,
    c9_route_gate, c10_lints, c11_landmarks,
]


def validate(m, survey=None, fast=False):
    """Run all contracts; return a flat list of Findings."""
    findings = []
    for fn in CONTRACTS:
        findings.extend(fn(m, survey, fast))
    return findings


def split(findings):
    errors = [f for f in findings if f.level == "error"]
    warnings = [f for f in findings if f.level == "warning"]
    return errors, warnings
