#!/usr/bin/env python3
"""Build retro.html — the single-file dashboard over the substrate tables.

Reads substrate/*.json (+ data/), computes a COMPACT viewmodel (aggregates and
top-Ns only — never the full decls table), injects it into ui_template.html as
window.RETRO, and emits ui/retro.html (gitignored; regenerate after a pool
refresh: python3 ui/build_ui.py).
"""
from __future__ import annotations
import json
from collections import Counter, defaultdict
from pathlib import Path

UI = Path(__file__).resolve().parent
SUB = UI.parent / "substrate"


def load(p):
    return json.loads(p.read_text())


commits = load(SUB / "commits.json")["commits"]
events_doc = load(SUB / "events.json")
events = events_doc["events"]
threads = load(SUB / "threads.json")

# ---- per-day pulse: build vs coordination vs other commits; lean/docs LoC
day = defaultdict(lambda: {"build": 0, "coord": 0, "other": 0, "lean": 0, "docs": 0,
                           "corrections": 0, "landings": 0})
for c in commits:
    d = c["author_iso"][:10]
    k = c["kind"]
    day[d]["build" if k in ("feat", "fix", "integrate", "refactor") else
           "coord" if k in ("doc", "docs", "tick") else "other"] += 1
    day[d]["lean"] += c["adds_lean"]; day[d]["docs"] += c["adds_docs"]
for ev in events:
    if ev.get("date") and {"corrected", "retracted", "refuted", "wall"} & set(ev["flags"]):
        day[ev["date"]]["corrections"] += 1
    if ev.get("date") and "landed" in ev["flags"]:
        day[ev["date"]]["landings"] += 1
days = sorted(d for d in day if d >= "2026-06-20")
cum_lean = cum_docs = 0
series = {"days": days, "build": [], "coord": [], "other": [], "corrections": [],
          "landings": [], "cum_lean": [], "cum_docs": [], "ratio": []}
for d in days:
    v = day[d]
    series["build"].append(v["build"]); series["coord"].append(v["coord"])
    series["other"].append(v["other"]); series["corrections"].append(v["corrections"])
    series["landings"].append(v["landings"])
    cum_lean += v["lean"]; cum_docs += v["docs"]
    series["cum_lean"].append(cum_lean); series["cum_docs"].append(cum_docs)
    series["ratio"].append(round(v["docs"] / v["lean"], 2) if v["lean"] > 400 else None)

# ---- structure (may be stale vs tip — carry its own anchor)
structure = {}
try:
    decls_meta = load(SUB / "decls.json")
    ds = decls_meta["decls"]
    cone = set(load(SUB / "cone.json")["cone"])
    rev = Counter()
    for dd in ds:
        for m in set(dd.get("deps_proof", []) + dd.get("deps_type", [])):
            rev[m] += 1
    files = {dd["name"]: dd["file"].split("/")[-1] for dd in ds}
    thms = sum(1 for dd in ds if dd["kind"] == "theorem")
    orphans = sum(1 for dd in ds if dd["kind"] == "theorem" and rev[dd["name"]] == 0)
    sorries = [dd["name"] for dd in ds if any("sorry" in a.lower() for a in dd.get("axioms", []))]
    allf = {dd["file"] for dd in ds}
    conef = {dd["file"] for dd in ds if dd["name"] in cone}
    structure = {
        "n_decls": len(ds), "n_theorems": thms, "cone_size": len(cone),
        "cone_pct": round(100 * len(cone) / len(ds)), "cone_files": len(conef),
        "total_files": len(allf), "sorry_decls": len(sorries),
        "sorries_on_cone": sum(1 for s in sorries if s in cone),
        "orphans": orphans, "orphan_pct": round(100 * orphans / max(thms, 1)),
        "zero_cone_files": len(allf - conef),
        "fan_in_top": [{"name": n.split(".")[-1], "file": files[n], "n": c}
                       for n, c in rev.most_common(60) if n in files][:12],
        "anchor": decls_meta.get("_meta", {}).get("generated", "see decls.json"),
    }
except FileNotFoundError:
    pass

# ---- error economy + knowledge debt (optional artifacts)
latency = []
try:
    latency = sorted(load(SUB / "latency_pairs.json"), key=lambda p: -p["hours"])[:10]
except FileNotFoundError:
    pass
debt_md = (SUB / "knowledge_debt.md")
debt_rows = []
if debt_md.exists():
    for ln in debt_md.read_text().splitlines():
        if ln.startswith("| `"):
            cells = [c.strip(" `*") for c in ln.strip("|").split("|")]
            debt_rows.append({"artifact": cells[0], "banked": cells[1],
                              "rediscovered": cells[2], "hours": cells[3], "note": cells[4]})

# ---- threads top
ttop = sorted(threads.items(), key=lambda kv: -kv[1]["adds_lean"])[:12]
threads_top = [{"slug": s, "lean": t["adds_lean"], "n": t["n_commits"],
                "span": f"{t['first_iso'][:10]}→{t['last_iso'][:10]}", "role": t["role"] or "—"}
               for s, t in ttop]

flag_counts = Counter(f for ev in events for f in ev["flags"])
sha_cls = Counter(r["cls"] for ev in events for r in ev.get("sha_refs_classified", []))

VM = {
    "generated_anchor": commits[0]["sha"] if commits else "?",
    "totals": {
        "commits": len(commits), "blocks": len(events),
        "block_range": f"{min(e['update_n'] for e in events)}–{max(e['update_n'] for e in events)}",
        "threads": len(threads), "lean_add": cum_lean, "docs_add": cum_docs,
        "ratio": round(cum_docs / max(cum_lean, 1), 2),
        "e1_pct": round(100 * sum(1 for e in events if e.get("landed_commit")) / len(events)),
        "a1": f"{sum(1 for e in events if e.get('date_quality') == 'ok')}/{sum(1 for e in events if e.get('landed_commit'))}",
    },
    "series": series, "structure": structure, "latency": latency,
    "debt": debt_rows, "threads_top": threads_top,
    "flags": dict(flag_counts.most_common(14)), "sha_cls": dict(sha_cls),
}

tpl = (UI / "ui_template.html").read_text()
out = tpl.replace("/*__RETRO_DATA__*/", "window.RETRO = " + json.dumps(VM) + ";")
(UI / "retro.html").write_text(out)
print(f"[build_ui] retro.html written ({len(out)//1024} KB); "
      f"views: pulse, loc, errors, debt, structure({'yes' if structure else 'NO decls.json'}), threads")
