#!/usr/bin/env python3
"""Build retro.html — the single-file dashboard over the substrate tables.

Reads substrate/*.json, data/*.json (combed chronicle), and — when present —
the snapshot-based LoC CSV from the diagnostic toolkit (aoyagi-loc-by-commit.csv,
searched locally then in ~/workspace/diagnostic-figures/aoyagi-report/). Computes
a COMPACT viewmodel (aggregates, buckets, top-Ns — never full tables), injects it
into ui_template.html as window.RETRO, emits ui/retro.html (gitignored).
"""
from __future__ import annotations
import csv as csvmod
import json
from collections import Counter, defaultdict
from pathlib import Path

UI = Path(__file__).resolve().parent
BASE = UI.parent
SUB = BASE / "substrate"
DATA = BASE / "data"

load = lambda p: json.loads(p.read_text())
commits = load(SUB / "commits.json")["commits"]
events = load(SUB / "events.json")["events"]
threads = load(SUB / "threads.json")

MILESTONES = [
    ("2026-06-20T14:36", "launch"), ("2026-06-28T10:56", "carve done"),
    ("2026-07-08T16:26", "L=2 headline"), ("2026-07-10T15:18", "(□) recalibration"),
    ("2026-07-11T10:13", "§5 lane directive"), ("2026-07-11T19:16", "DecoratedDescent"),
    ("2026-07-12T08:39", "minAdm=cCodim"), ("2026-07-13T17:23", "Brick F"),
    ("2026-07-13T21:28", "adm fix"),
]

# ---------- per-day pulse + numstat fallback LoC
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
series = {"days": days, "build": [], "coord": [], "other": [],
          "corrections": [], "landings": [], "ratio": []}
cum_lean = cum_docs = 0
for d in days:
    v = day[d]
    for k in ("build", "coord", "other", "corrections", "landings"):
        series[k].append(v[k])
    cum_lean += v["lean"]; cum_docs += v["docs"]
    series["ratio"].append(round(v["docs"] / v["lean"], 2) if v["lean"] > 400 else None)

# ---------- snapshot-based 3-metric LoC + churn + pillar stack (diagnostic CSV)
loc3 = None
for cand in (BASE / "aoyagi-loc-by-commit.csv",
             Path.home() / "workspace/diagnostic-figures/aoyagi-report/aoyagi-loc-by-commit.csv"):
    if cand.exists():
        rows = list(csvmod.DictReader(cand.open()))
        pillar_cols = [k for k in rows[0] if k.startswith("pillar::")]
        bucket = {}
        for r in rows:  # 6h buckets: keep last cumulative, sum churn
            t = r["author_time"][:11] + f"{int(r['author_time'][11:13])//6*6:02d}"
            b = bucket.setdefault(t, {"add": 0, "del": 0})
            b["raw"] = int(r["lean_raw_loc"]); b["native"] = int(r["lean_native_token_loc"])
            b["prose"] = int(r["nonlean_loc"])
            d = int(r["lean_raw_delta"] or 0)
            b["add"] += max(d, 0); b["del"] += max(-d, 0)
            for pc in pillar_cols:
                b[pc] = int(r[pc])
        ts = sorted(bucket)
        top = sorted(pillar_cols, key=lambda pc: -bucket[ts[-1]].get(pc, 0))
        keep, fold = top[:7], top[7:]
        loc3 = {"t": ts, "raw": [bucket[t]["raw"] for t in ts],
                "native": [bucket[t]["native"] for t in ts],
                "prose": [bucket[t]["prose"] for t in ts],
                "add": [bucket[t]["add"] for t in ts],
                "del": [bucket[t]["del"] for t in ts],
                "pillars": {pc.split("::")[1]: [bucket[t].get(pc, 0) for t in ts] for pc in keep},
                "csv_anchor": cand.name + " (snapshot run; regenerate via generate_loc.py for tip)"}
        if fold:
            loc3["pillars"]["other"] = [sum(bucket[t].get(pc, 0) for pc in fold) for t in ts]
        break

# ---------- structure (kernel walker outputs)
structure = {}
try:
    dm = load(SUB / "decls.json"); ds = dm["decls"]
    cone = set(load(SUB / "cone.json")["cone"])
    rev = Counter()
    for dd in ds:
        for m in set(dd.get("deps_proof", []) + dd.get("deps_type", [])):
            rev[m] += 1
    files = {dd["name"]: dd["file"].split("/")[-1] for dd in ds}
    thms = sum(1 for dd in ds if dd["kind"] == "theorem")
    orphans = sum(1 for dd in ds if dd["kind"] == "theorem" and rev[dd["name"]] == 0)
    sorries = [dd["name"] for dd in ds if any("sorry" in a.lower() for a in dd.get("axioms", []))]
    allf = {dd["file"] for dd in ds}; conef = {dd["file"] for dd in ds if dd["name"] in cone}
    structure = {"n_decls": len(ds), "cone_size": len(cone),
                 "cone_pct": round(100 * len(cone) / len(ds)),
                 "cone_files": len(conef), "total_files": len(allf),
                 "sorry_decls": len(sorries),
                 "sorries_on_cone": sum(1 for s in sorries if s in cone),
                 "orphans": orphans, "orphan_pct": round(100 * orphans / max(thms, 1)),
                 "zero_cone_files": len(allf - conef),
                 "fan_in_top": [{"name": n.split(".")[-1], "file": files[n], "n": c}
                                for n, c in rev.most_common(60) if n in files][:12],
                 "anchor": dm.get("_meta", {}).get("generated", "?")}
except FileNotFoundError:
    pass

# ---------- error economy + knowledge debt
latency = []
try:
    latency = sorted(load(SUB / "latency_pairs.json"), key=lambda p: -p["hours"])[:10]
except FileNotFoundError:
    pass
debt_rows = []
if (SUB / "knowledge_debt.md").exists():
    for ln in (SUB / "knowledge_debt.md").read_text().splitlines():
        if ln.startswith("| `"):
            c = [x.strip(" `*") for x in ln.strip("|").split("|")]
            debt_rows.append({"artifact": c[0], "banked": c[1], "rediscovered": c[2],
                              "hours": c[3], "note": c[4]})

# ---------- swimlane (top threads by lean, spans) + combed chronicle summaries
swim = []
for s, t in sorted(threads.items(), key=lambda kv: -kv[1]["adds_lean"])[:40]:
    if t["first_iso"] and t["first_iso"] >= "2026-06-20":
        swim.append({"slug": s, "start": t["first_iso"], "end": t["last_iso"],
                     "lean": t["adds_lean"], "n": t["n_commits"],
                     "role": t["role"] or "—", "pillar": t["pillar"] or "other"})
swim.sort(key=lambda r: r["start"])

dag, combed = {}, {}
try:
    proc = load(DATA / "process.json")
    pl = {t["thread"]: t.get("pillar_fed", "other") for t in proc["threads"]}
    dag = {"nodes": [{"name": t["thread"], "pillar": pl[t["thread"]],
                      "title": t.get("title", "")[:60]} for t in proc["threads"]],
           "links": [{"source": e["from"], "target": e["to"], "rel": e["relation"]}
                     for e in proc["edges"]
                     if e["from"] in pl and e["to"] in pl]}
    claims = load(DATA / "claims.json")
    dec = load(DATA / "decorrelation.json")
    rc = load(DATA / "routes_concepts.json")
    combed = {"claims": dict(Counter(c["status"] for c in claims["claims_lifecycle"])),
              "channels": dict(Counter(c["channel"] for c in dec["catches"])),
              "concepts": dict(Counter(c["pillar"] for c in rc["concepts"]).most_common(7)),
              "note": "combed by five decorrelated log-reading agents (snapshot ~UPDATE-975); S-grade"}
except FileNotFoundError:
    pass

VM = {"anchor": commits[0]["sha"] if commits else "?",
      "totals": {"commits": len(commits), "blocks": len(events),
                 "block_range": f"{min(e['update_n'] for e in events)}–{max(e['update_n'] for e in events)}",
                 "threads": len(threads), "lean_add": cum_lean, "docs_add": cum_docs,
                 "ratio": round(cum_docs / max(cum_lean, 1), 2),
                 "e1_pct": round(100 * sum(1 for e in events if e.get("landed_commit")) / len(events)),
                 "a1": f"{sum(1 for e in events if e.get('date_quality') == 'ok')}/{sum(1 for e in events if e.get('landed_commit'))}"},
      "series": series, "loc3": loc3, "structure": structure, "latency": latency,
      "debt": debt_rows, "swim": swim, "milestones": MILESTONES, "dag": dag,
      "combed": combed,
      "sha_cls": dict(Counter(r["cls"] for ev in events
                              for r in ev.get("sha_refs_classified", [])))}

tpl = (UI / "ui_template.html").read_text()
(UI / "retro.html").write_text(
    tpl.replace("/*__RETRO_DATA__*/", "window.RETRO = " + json.dumps(VM) + ";"))
print(f"[build_ui] retro.html ({(UI/'retro.html').stat().st_size//1024} KB); "
      f"loc3={'csv' if loc3 else 'ABSENT'}, structure={'yes' if structure else 'NO'}, "
      f"swim={len(swim)}, dag={len(dag.get('nodes', []))}n/{len(dag.get('links', []))}e")
