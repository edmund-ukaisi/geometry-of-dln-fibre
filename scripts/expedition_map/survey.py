"""The survey: a computed join of ``claims.yaml`` against a Lean-walker dump.

Regenerated, never edited (spec: "cannot rot"). The walker dump comes in two
real shapes, so the adapter is defensive and records which *mode* it built in:

* **full** -- a dict/list of decl records, each with ``deps_type``/``deps_proof``
  and ``axioms`` (the ``decls.json`` shape). Existence, sorry-taint and
  discharge-edge witnessing are all definitive.
* **cone**  -- a dict with a ``cone`` list of decl *names* (+ optional
  ``headlines``), the ``cone_before_mint.json`` shape. This is the transitive
  dependency cone of already-proven roots: it can *confirm* a decl is present
  (in-cone => exists, sorry-free), but it cannot *refute* existence (a decl
  outside the roots' cone may simply be live frontier), and it carries no
  per-decl deps/axioms. Survey-dependent checks degrade to warnings, honestly.

The adapter keys node<->decl by exact Lean name or by last-dotted-component
(short name), because ``claims.yaml`` anchors are usually unqualified.
"""

from __future__ import annotations

import json
import subprocess
import datetime
from pathlib import Path

from . import model

SORRY_AXIOM = "sorryAx"


# ---------------------------------------------------------------------------
# Walker-dump adapter
# ---------------------------------------------------------------------------

def adapt_walker(data):
    """Normalize a walker dump into a uniform record set.

    Returns ``{mode, decls, names, cone, headlines, root_prefix}`` where
    ``decls`` maps full-name -> {axioms, deps_type, deps_proof, sorry, module,
    file, line}. In cone mode ``decls`` is empty and only ``names``/``cone`` are
    populated.
    """
    decls = {}
    names = set()
    cone = None
    headlines = []
    root_prefix = None

    def ingest_decl_list(lst):
        for d in lst:
            if isinstance(d, str):
                names.add(d)
                continue
            if not isinstance(d, dict) or "name" not in d:
                continue
            name = d["name"]
            names.add(name)
            decls[name] = {
                "axioms": list(d.get("axioms", [])),
                "deps_type": list(d.get("deps_type", [])),
                "deps_proof": list(d.get("deps_proof", [])),
                "sorry": SORRY_AXIOM in d.get("axioms", []),
                "module": d.get("module", ""),
                "file": d.get("file", ""),
                "line": d.get("line"),
            }

    if isinstance(data, list):
        ingest_decl_list(data)
    elif isinstance(data, dict):
        meta = data.get("_meta", {})
        root_prefix = meta.get("root_prefix")
        if isinstance(data.get("decls"), list):
            ingest_decl_list(data["decls"])
        if isinstance(data.get("cone"), list):
            cone = set(x for x in data["cone"] if isinstance(x, str))
            names.update(cone)
        headlines = list(data.get("headlines", []))
    else:
        raise ValueError("walker dump: expected a list or a dict")

    mode = "full" if decls else "cone"
    return {
        "mode": mode,
        "decls": decls,
        "names": names,
        "cone": cone,
        "headlines": headlines,
        "root_prefix": root_prefix,
    }


def _index_by_short(names):
    idx = {}
    for n in names:
        idx.setdefault(model.short_name(n), []).append(n)
    return idx


def _resolve_lean(lean, walker, short_idx):
    """Map a node's ``lean`` anchor to a full decl name in the walker set.

    Returns (full_name | None, exact_bool). Exact match wins; otherwise a unique
    short-name match; ambiguous short matches return None (surfaced by callers).
    """
    if not lean:
        return None, False
    if lean in walker["names"]:
        return lean, True
    cands = short_idx.get(model.short_name(lean), [])
    if len(cands) == 1:
        return cands[0], False
    return None, False


def _transitive_deps(full_name, decls, cap=20000):
    """All decls reachable via deps_type ∪ deps_proof from ``full_name``."""
    seen = set()
    stack = [full_name]
    while stack and len(seen) < cap:
        cur = stack.pop()
        rec = decls.get(cur)
        if not rec:
            continue
        for dep in rec["deps_type"] + rec["deps_proof"]:
            if dep not in seen:
                seen.add(dep)
                stack.append(dep)
    return seen


# ---------------------------------------------------------------------------
# Git / freshness
# ---------------------------------------------------------------------------

def git_head(cwd):
    try:
        out = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=str(cwd),
            capture_output=True, text=True, timeout=10,
        )
        if out.returncode == 0:
            return out.stdout.strip()
    except Exception:
        pass
    return None


# ---------------------------------------------------------------------------
# Build
# ---------------------------------------------------------------------------

def build_survey(m, data, source_path):
    """Compute the survey join for map ``m`` against walker dump ``data``."""
    walker = adapt_walker(data)
    short_idx = _index_by_short(walker["names"])
    decls = walker["decls"]

    per_node = {}
    for n in m["nodes"]:
        nid = n["id"]
        lean = n.get("lean")
        full, exact = _resolve_lean(lean, walker, short_idx)
        entry = {
            "lean": lean,
            "resolved": full,
            "match": ("exact" if exact else ("short" if full else "none")),
            "in_cone": None,
            "lean_exists": None,     # True / False / None(unknown, cone mode)
            "sorry_tainted": None,   # True / False / None(unknown)
            "sorry_cone": None,      # list of sorried decls in transitive closure
        }
        if lean:
            if walker["cone"] is not None:
                entry["in_cone"] = full is not None and full in walker["cone"]
            if walker["mode"] == "full":
                entry["lean_exists"] = full is not None
                rec = decls.get(full) if full else None
                if rec is not None:
                    entry["sorry_tainted"] = rec["sorry"]
                    tdeps = _transitive_deps(full, decls)
                    tainted = sorted(
                        d for d in ({full} | tdeps)
                        if decls.get(d, {}).get("sorry")
                    )
                    entry["sorry_cone"] = tainted
                    entry["sorry_tainted"] = bool(tainted) or rec["sorry"]
            else:  # cone mode: confirm-only
                entry["lean_exists"] = True if entry["in_cone"] else None
                entry["sorry_tainted"] = False if entry["in_cone"] else None
        per_node[nid] = entry

    # Discharge-edge witnessing (full mode only; else UNKNOWN).
    witness = {}
    for n in m["nodes"]:
        for e in n["edges"]:
            if e["type"] != "discharges":
                continue
            provider, consumer = n["id"], e["to"]
            key = f"{provider}->{consumer}"
            cnode = m["by_id"].get(consumer)
            pfull = per_node.get(provider, {}).get("resolved")
            cfull = per_node.get(consumer, {}).get("resolved")
            info = {
                "provider": provider, "consumer": consumer,
                "witnessed": None, "reason": "",
            }
            if walker["mode"] != "full":
                info["reason"] = "cone-mode survey: dep data unavailable"
            elif cnode is None:
                info["reason"] = "consumer not in map"
            elif not cfull:
                info["reason"] = "consumer lean anchor not found"
            elif not pfull:
                info["reason"] = "provider lean anchor not found"
            else:
                tdeps = _transitive_deps(cfull, decls)
                info["witnessed"] = pfull in tdeps
                if not info["witnessed"]:
                    info["reason"] = "provider absent from consumer's transitive deps"
            witness[key] = info

    # Live-sorry cone from roots (full mode): sorried decls reachable from a root
    # node's anchor. Reported as node-anchored so contract 5 can check membership.
    live_sorry = []
    if walker["mode"] == "full":
        seen = set()
        for r in m["meta"].get("roots", []):
            rfull = per_node.get(r, {}).get("resolved")
            if not rfull:
                continue
            for d in ({rfull} | _transitive_deps(rfull, decls)):
                if decls.get(d, {}).get("sorry") and d not in seen:
                    seen.add(d)
        live_sorry = sorted(seen)

    # Orphans: open nodes not weakly connected to any root.
    reach = model.reachable_from_roots(m)
    orphans = [n["id"] for n in m["nodes"]
               if model.is_open(n) and n["id"] not in reach]

    freshness = {
        "source": str(source_path),
        "git_head": git_head(m["map_dir"]),
        "generated": datetime.datetime.now(datetime.timezone.utc)
        .isoformat(timespec="seconds"),
        "walker_mode": walker["mode"],
        "walker_generated": (
            data.get("_meta", {}).get("generated") if isinstance(data, dict) else None
        ),
        "n_decls": len(walker["names"]),
    }
    return {
        "freshness": freshness,
        "nodes": per_node,
        "witness": witness,
        "live_sorry": live_sorry,
        "orphans": orphans,
        "headlines": walker["headlines"],
    }


def write_survey(m, survey):
    out_dir = Path(m["map_dir"]) / "survey"
    out_dir.mkdir(exist_ok=True)
    path = out_dir / "survey.json"
    with open(path, "w") as fh:
        json.dump(survey, fh, indent=2, sort_keys=True)
    return path


def load_survey(m):
    """Load ``survey/survey.json`` if present; annotate staleness vs git HEAD."""
    path = Path(m["map_dir"]) / "survey" / "survey.json"
    if not path.is_file():
        return None
    with open(path) as fh:
        survey = json.load(fh)
    head = git_head(m["map_dir"])
    stamped = survey.get("freshness", {}).get("git_head")
    survey["_stale"] = bool(head and stamped and head != stamped)
    survey["_current_head"] = head
    return survey


# ---------------------------------------------------------------------------
# history cache (per-sha snapshots; keeps survey.json readable)
# ---------------------------------------------------------------------------

def load_history_cache(m):
    path = Path(m["map_dir"]) / "survey" / "history-cache.json"
    if path.is_file():
        with open(path) as fh:
            return json.load(fh)
    return {}


def write_history_cache(m, cache):
    out_dir = Path(m["map_dir"]) / "survey"
    out_dir.mkdir(exist_ok=True)
    with open(out_dir / "history-cache.json", "w") as fh:
        json.dump(cache, fh, indent=2, sort_keys=True)


# ---------------------------------------------------------------------------
# cordon (§ blueprint leak audit) — emitted by the Lean side, consumed by validate
# ---------------------------------------------------------------------------

def load_cordon(m):
    """Load ``survey/cordon.json`` if present, else None.

    Schema: {roots:[], unaccounted:[<decl>], cited:[{axiom,source}],
             leaks:[{decl, via}]}.
    """
    path = Path(m["map_dir"]) / "survey" / "cordon.json"
    if not path.is_file():
        return None
    with open(path) as fh:
        return json.load(fh)
