#!/usr/bin/env python3
"""Knowledge-debt readouts (burden-of-knowledge framing, PLAN.md §Framing).

1. Coordination-share curve: cumulative docs-LoC vs lean-LoC ratio per day, and
   docs-kind commit fraction per day (from commits.json).
2. Time-to-rediscovery: for each "found already banked" event, banked-date via
   git pickaxe (earliest commit introducing the artifact name) vs the recorded
   rediscovery moment; the gap is the debt made visible.
"""
from __future__ import annotations
import json, subprocess
from collections import defaultdict
from datetime import datetime
from pathlib import Path

D = Path(__file__).resolve().parent
REPO = D.parents[4]
BRANCH = "origin/expedition/aoyagi-full"
commits = json.loads((D / "commits.json").read_text())["commits"]

# ---- 1. coordination share
day = defaultdict(lambda: {"lean": 0, "docs": 0, "n_doc": 0, "n_feat": 0})
for c in commits:
    d = c["author_iso"][:10]
    day[d]["lean"] += c["adds_lean"]; day[d]["docs"] += c["adds_docs"]
    k = c["kind"]
    if k in ("doc", "docs", "tick"): day[d]["n_doc"] += 1
    elif k in ("feat", "fix"): day[d]["n_feat"] += 1

S = ["# Knowledge-debt readouts", "", "## Coordination share per day",
     "", "| day | docs LoC | lean LoC | docs:lean | doc-commits | feat+fix |", "|---|---|---|---|---|---|"]
cl = cd = 0
for d in sorted(day):
    v = day[d]; cl += v["lean"]; cd += v["docs"]
    r = v["docs"] / v["lean"] if v["lean"] else float("inf")
    S.append(f"| {d} | {v['docs']:,} | {v['lean']:,} | {r:.2f} | {v['n_doc']} | {v['n_feat']} |")
S += ["", f"**Cumulative**: docs {cd:,} vs lean {cl:,} → ratio {cd/max(cl,1):.2f}", ""]

# ---- 2. time-to-rediscovery
# (artifact searched via pickaxe; rediscovery moments from the ledger record)
EVENTS = [
    ("routeMBoxThresholdFinite_mnp", "2026-07-13T14:06", "mnp base case, 1st rediscovery (endgame parallelization)"),
    ("routeMBoxThresholdFinite_mnp", "2026-07-14T00:58", "mnp base case, 2nd rediscovery (waist L=0, different lane)"),
    ("sjGoodChartLoss_endpoint_lt_top", "2026-07-11T08:54", "native inner slice (UPDATE-883, casting detour abandoned)"),
    ("minAdm_eq_frontPeel", "2026-07-11T21:13", "α-unlock scoped as fresh build, was banked identity (UPDATE-933)"),
]


def banked_date(name: str):
    out = subprocess.run(["git", "log", "-S", name, "--format=%aI", "413566b3.." + BRANCH],
                         cwd=REPO, text=True, stdout=subprocess.PIPE).stdout.split()
    return out[-1] if out else None  # oldest = introduction


S += ["## Time-to-rediscovery (found-already-banked events)", "",
      "| artifact | banked | rediscovered | debt (h) | note |", "|---|---|---|---|---|"]
for name, redisc, note in EVENTS:
    b = banked_date(name)
    if b:
        hrs = (datetime.fromisoformat(redisc + ":00+00:00") - datetime.fromisoformat(b)).total_seconds() / 3600
        S.append(f"| `{name}` | {b[:16]} | {redisc} | **{hrs:.0f}** | {note} |")
    else:
        S.append(f"| `{name}` | NOT FOUND | {redisc} | — | {note} (pickaxe miss — name may differ at banking) |")
S += ["", "Debt hours = the artifact sat in the tree, needed and unfound. The duplicated mnp row is",
      "the sharpest datum: the SAME theorem was independently rediscovered twice, ~11h apart,",
      "by different lanes — an index failure repeating after it was already once exposed.", ""]

(D / "knowledge_debt.md").write_text("\n".join(S) + "\n")
print("\n".join(S[-24:]))
