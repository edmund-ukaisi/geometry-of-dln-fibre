"""Views: joins of heart x survey x overlay, rendered (never edited).

``STATUS.md`` is the only materialized view (tick). The rest print to stdout at
graded resolution. Ambient views stay thin so decision/brief views can be rich
(the value-density principle).
"""

from __future__ import annotations

from pathlib import Path

from . import model


# ---------------------------------------------------------------------------
# Graph helpers
# ---------------------------------------------------------------------------

def _adj_and_reverse(m):
    adj = model.build_dep_graph(m)          # X -> Y : X depends on Y
    rev = {v: set() for v in adj}
    for v, ws in adj.items():
        for w in ws:
            rev[w].add(v)
    return adj, rev


def _transitive(adj, start):
    seen, stack = set(), [start]
    while stack:
        v = stack.pop()
        for w in sorted(adj.get(v, ())):
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return seen


def _title(m, nid):
    n = m["by_id"].get(nid)
    return n.get("title", "") if n else "(missing)"


def _fmt(m, nid, width=44):
    n = m["by_id"].get(nid)
    if not n:
        return f"{nid} (missing)"
    t = n.get("title", "")
    if len(t) > width:
        t = t[: width - 1] + "…"
    return f"{nid} [{n['status']}] {t}"


# ---------------------------------------------------------------------------
# tick / STATUS.md
# ---------------------------------------------------------------------------

def render_status(m, survey):
    slug = m["meta"].get("expedition", "?")
    updated = m["meta"].get("updated", "?")
    roots = m["meta"].get("roots", [])
    lines = [f"# STATUS — {slug}", ""]

    head = ""
    if survey:
        fh = survey.get("freshness", {})
        sha = (fh.get("git_head") or "")[:8]
        stale = " (STALE vs HEAD)" if survey.get("_stale") else ""
        head = f"survey: {fh.get('walker_mode', '?')}-mode @ {sha or 'no-git'}{stale}"
    lines.append(f"updated: {updated}    {head}".rstrip())

    reach = model.reachable_from_roots(m)
    open_reach = [n for n in m["nodes"] if model.is_open(n) and n["id"] in reach]
    lines.append("")
    lines.append(f"## roots ({len(roots)}) — {len(open_reach)} open nodes below")
    for r in roots:
        n = m["by_id"].get(r)
        st = n["status"] if n else "MISSING"
        lines.append(f"  ◦ {r} [{st}] {_title(m, r)}")

    # Live frontier: open nodes whose dependency-providers are all closed (ready)
    # vs blocked. Ordered ready-first.
    adj, _ = _adj_and_reverse(m)
    ready, blocked = [], []
    for n in open_reach:
        deps = adj.get(n["id"], set())
        if all(model.is_closed(m["by_id"][d]) for d in deps if d in m["by_id"]):
            ready.append(n)
        else:
            blocked.append(n)
    lines.append("")
    lines.append(f"## live frontier — {len(ready)} ready, {len(blocked)} blocked")
    for n in ready + blocked:
        flag = "▶" if n in ready else "·"
        owner = n.get("owner") or "UNOWNED"
        lines.append(f"  {flag} {n['id']} [{n['status']}] owner={owner}")

    # Open gates: routes awaiting adoption + unwitnessed discharge edges.
    gates = []
    for n in m["nodes"]:
        if n["kind"] == "route" and n["status"] == "proposed":
            gates.append(f"route {n['id']} awaiting adoption gate")
    unwit = 0
    if survey:
        for info in survey.get("witness", {}).values():
            consumer = m["by_id"].get(info.get("consumer"))
            if consumer and not model.at_least(consumer, "skeleton-linked"):
                continue  # contract 4 only gates once the consumer is in the skeleton
            if info.get("witnessed") is not True:
                unwit += 1
    if unwit:
        gates.append(f"{unwit} discharge edge(s) UNWITNESSED")
    if gates:
        lines.append("")
        lines.append("## open gates")
        for g in gates[:6]:
            lines.append(f"  ! {g}")

    warns = []
    if survey and survey.get("_stale"):
        warns.append("survey stale vs git HEAD — run `expedition survey`")
    if survey and survey.get("orphans"):
        warns.append(f"orphaned open nodes: {', '.join(survey['orphans'])}")
    if warns:
        lines.append("")
        lines.append("## staleness / drift")
        for w in warns:
            lines.append(f"  ⚠ {w}")

    return "\n".join(lines) + "\n"


def write_status(m, survey):
    text = render_status(m, survey)
    path = Path(m["map_dir"]) / "STATUS.md"
    path.write_text(text)
    return path, text


# ---------------------------------------------------------------------------
# decision view
# ---------------------------------------------------------------------------

def render_decision(m, survey, nid):
    n = m["by_id"].get(nid)
    if not n:
        return f"no such node: {nid}"
    adj, rev = _adj_and_reverse(m)
    out = [f"# decision: {nid}", ""]
    out.append(f"kind={n['kind']}  status={n['status']}  tier={n.get('tier')}  "
               f"owner={n.get('owner') or 'UNOWNED'}")
    if n.get("lean"):
        out.append(f"lean: {n['lean']}")
    if n.get("kill"):
        out.append(f"kill: {n['kill']}")
    out.append("")
    out.append(f"title: {n.get('title', '')}")
    if n.get("prop"):
        out.append("prop:")
        out.extend("    " + ln for ln in str(n["prop"]).rstrip().splitlines())
    if n.get("notes"):
        out.append(f"notes: {n['notes']}")

    if survey and nid in survey.get("nodes", {}):
        s = survey["nodes"][nid]
        out += ["", "## kernel (survey)",
                f"  resolved={s.get('resolved')}  match={s.get('match')}  "
                f"exists={s.get('lean_exists')}  sorry={s.get('sorry_tainted')}"]

    out += ["", "## cone up (consumers → roots)"]
    for a in sorted(_transitive(rev, nid)):
        out.append("  ↑ " + _fmt(m, a))
    out += ["", "## cone down (this needs / rests on)"]
    for d in sorted(_transitive(adj, nid)):
        out.append("  ↓ " + _fmt(m, d))

    # Siblings under shared parents (co-providers of this node's consumers).
    sibs = set()
    for parent in rev.get(nid, ()):
        sibs |= adj.get(parent, set())
    sibs.discard(nid)
    out += ["", "## siblings (co-inputs to the same consumers)"]
    for s in sorted(sibs):
        out.append("  • " + _fmt(m, s))

    # Refuted siblings anywhere in the map, with battery pointers.
    refuted = [x for x in m["nodes"] if x["status"] == "refuted"]
    if refuted:
        out += ["", "## refuted siblings (dead routes + witnesses)"]
        for x in refuted:
            batt = x.get("kill") or "(no battery)"
            out.append(f"  ✗ {x['id']}: {x.get('notes') or x.get('title')}  [{batt}]")

    out += ["", "## evidence"]
    for e in n.get("evidence", []) or ["(none)"]:
        out.append(f"  - {e}")
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------------------
# lookahead view
# ---------------------------------------------------------------------------

def render_lookahead(m, survey):
    adj, _ = _adj_and_reverse(m)
    open_ids = {n["id"] for n in m["nodes"] if model.is_open(n)}

    build_time, sorry_prop, idle, unwit = [], [], [], []
    for nid in sorted(open_ids):
        deps = adj.get(nid, set())
        open_deps = [d for d in deps if d in open_ids]
        if open_deps:
            build_time.append((nid, open_deps))
        else:
            # buildable now: inputs closed. If any input is sorry-tainted it is
            # a sorry-propagation dep (can build against a sorried input).
            tainted = []
            if survey:
                for d in deps:
                    if survey["nodes"].get(d, {}).get("sorry_tainted"):
                        tainted.append(d)
            if tainted:
                sorry_prop.append((nid, tainted))

    for n in m["nodes"]:
        owner = (n.get("owner") or "")
        if model.is_open(n) and (not owner or owner.startswith("parked")):
            idle.append(n["id"])

    if survey:
        for k, info in survey.get("witness", {}).items():
            if info.get("witnessed") is not True:
                unwit.append((k, info.get("reason", "")))

    head = []
    head.append(f"open nodes: {len(open_ids)}")
    head.append(f"build-time-blocked (need open siblings): {len(build_time)}")
    head.append(f"sorry-propagation (buildable vs sorried input): {len(sorry_prop)}")
    head.append(f"idle / parked: {len(idle)}")
    head.append(f"unwitnessed discharge edges: {len(unwit)}")
    if survey and survey.get("orphans"):
        head.append(f"orphans: {len(survey['orphans'])}")
    out = ["# lookahead", "", "## headline"] + [f"  - {h}" for h in head[:7]]

    out += ["", "## build-time dependencies (open → open)"]
    for nid, deps in build_time:
        out.append(f"  {nid} ⇐ {', '.join(sorted(deps))}")
    out += ["", "## sorry-propagation (buildable now against sorried inputs)"]
    for nid, deps in sorry_prop:
        out.append(f"  {nid} ⇠ {', '.join(model.short_name(d) for d in deps)}")
    out += ["", "## idle / parked"]
    for nid in idle:
        n = m["by_id"][nid]
        out.append(f"  {nid} owner={n.get('owner') or 'UNOWNED'}")
    out += ["", "## unwitnessed discharge edges"]
    for k, reason in unwit:
        out.append(f"  {k}  ({reason})")
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------------------
# dag view
# ---------------------------------------------------------------------------

def render_dag(m, kind=None, status=None):
    out = ["# dag"]
    sel = [n for n in m["nodes"]
           if (kind is None or n["kind"] == kind)
           and (status is None or n["status"] == status)]
    ids = {n["id"] for n in sel}
    by_kind = {}
    for n in sel:
        by_kind.setdefault(n["kind"], []).append(n)
    for k in sorted(by_kind):
        out.append("")
        out.append(f"## {k}")
        for n in by_kind[k]:
            out.append(f"  {n['id']} [{n['status']}]")
            for e in n["edges"]:
                mark = "→" if e["type"] in model.DEP_EDGE_TYPES else "⇥"
                vis = "" if (e["to"] in ids or not (kind or status)) else "  (filtered)"
                out.append(f"      {mark} {e['type']}: {e['to']}{vis}")
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------------------
# brief view (teammate context bundle, resolutions 1-4, cumulative)
# ---------------------------------------------------------------------------

def _read_overlay_cards(map_dir):
    cards = []
    d = Path(map_dir) / "overlay" / "cards"
    if d.is_dir():
        for p in sorted(d.glob("*.md")):
            cards.append((p.name, p.read_text()))
    return cards


def _read_overlay_file(map_dir, name):
    p = Path(map_dir) / "overlay" / name
    return p.read_text() if p.is_file() else ""


def render_brief(m, survey, nid, resolution):
    n = m["by_id"].get(nid)
    if not n:
        return f"no such node: {nid}", 0
    resolution = max(1, min(4, int(resolution)))
    adj, rev = _adj_and_reverse(m)
    up = sorted(_transitive(rev, nid))
    down = sorted(_transitive(adj, nid))
    family = {nid} | set(up) | set(down)

    body = [f"# brief: {nid}  (resolution {resolution})", ""]

    # --- resolution 1: node + edges ---
    body.append(f"kind={n['kind']}  status={n['status']}  "
                f"owner={n.get('owner') or 'UNOWNED'}")
    if n.get("lean"):
        body.append(f"lean: {n['lean']}")
    body.append(f"title: {n.get('title', '')}")
    if n.get("notes"):
        body.append(f"notes: {n['notes']}")
    body.append("edges:")
    for e in n["edges"]:
        body.append(f"  {e['type']} -> {e['to']}")

    # --- resolution 2: ancestors-to-root + siblings + battery names ---
    if resolution >= 2:
        body += ["", "## ancestors → root"]
        for a in up:
            body.append(f"  ↑ {a}: {_title(m, a)}")
        sibs = set()
        for parent in rev.get(nid, ()):
            sibs |= adj.get(parent, set())
        sibs.discard(nid)
        body += ["", "## siblings"]
        for s in sorted(sibs):
            body.append(f"  • {s}: {_title(m, s)}")
        body += ["", "## battery (attached to family)"]
        for fid in sorted(family):
            fn = m["by_id"].get(fid)
            if fn and fn.get("kill"):
                body.append(f"  {fid}: {fn['kill']}")

    # --- resolution 3: overlay cards touching family + dead routes ---
    if resolution >= 3:
        body += ["", "## banked / near-miss cards"]
        for name, text in _read_overlay_cards(m["map_dir"]):
            if any(fid in text for fid in family) or not family:
                first = next((ln for ln in text.splitlines() if ln.strip()), name)
                body.append(f"  [{name}] {first.lstrip('# ').strip()}")
        body += ["", "## dead routes (reasons + witnesses)"]
        for x in m["nodes"]:
            if x["status"] in ("refuted", "superseded", "retired"):
                batt = x.get("kill") or "—"
                body.append(f"  ✗ {x['id']}: {x.get('notes') or x.get('title')}  [{batt}]")

    # --- resolution 4: full prop texts of the cone + survey status ---
    if resolution >= 4:
        body += ["", "## cone prop texts"]
        for fid in [nid] + [x for x in sorted(family) if x != nid]:
            fn = m["by_id"].get(fid)
            if not fn:
                continue
            body.append(f"### {fid} [{fn['status']}]")
            if fn.get("prop"):
                body.extend("    " + ln for ln in str(fn["prop"]).rstrip().splitlines())
            else:
                body.append("    (no prop stated)")
        if survey:
            body += ["", "## survey status per family node"]
            for fid in sorted(family):
                s = survey["nodes"].get(fid, {})
                body.append(f"  {fid}: exists={s.get('lean_exists')} "
                            f"sorry={s.get('sorry_tainted')} match={s.get('match')}")

    text = "\n".join(body) + "\n"
    est_tokens = len(text) // 4
    header = f"[≈{est_tokens} tokens | resolution {resolution}]\n"
    return header + text, est_tokens
