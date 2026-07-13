#!/usr/bin/env python3
"""Structure readouts over decls.json → cone.json + structure_summary.md.

All H-grade: reverse-reachability cone of the headline(s), sorry-footprint vs
cone check, fan-in ranking (de-facto API), orphan inventory, per-file/pillar
cone shares.
"""
from __future__ import annotations
import json
from collections import Counter, defaultdict, deque
from pathlib import Path

D = Path(__file__).resolve().parent
doc = json.loads((D / "decls.json").read_text())
decls = {d["name"]: d for d in doc["decls"]}

HEADLINES = [
    "DLNFibre.DLN.RLCT.aoyagi_learning_coefficient_gen",
    "DLNFibre.DLN.RLCT.aoyagi_learning_coefficient_L2",
    "DLNFibre.DLN.RLCT.aoyagi_learning_coefficient_gen_le",
]
HEADLINES = [h for h in HEADLINES if h in decls] or \
            [n for n in decls if n.endswith("aoyagi_learning_coefficient_gen")]

deps = {n: sorted(set(d.get("deps_proof", []) + d.get("deps_type", [])) & set(decls))
        for n, d in decls.items()}
rev = defaultdict(set)
for n, ds in deps.items():
    for m in ds:
        rev[m].add(n)


def cone_of(roots):
    seen, q = set(roots), deque(roots)
    while q:
        for m in deps.get(q.popleft(), []):
            if m not in seen:
                seen.add(m); q.append(m)
    return seen


cone = cone_of(HEADLINES)
sorries = {n for n, d in decls.items() if any("sorry" in a.lower() for a in d.get("axioms", []))}
sorry_in_cone = sorted(sorries & cone)

fan_in = Counter({n: len(rev[n]) for n in decls if rev[n]})
thm_orphans = [n for n, d in decls.items()
               if d["kind"] == "theorem" and not rev[n] and n not in HEADLINES]

file_of = {n: d["file"] for n, d in decls.items()}
cone_files = Counter(file_of[n] for n in cone)
all_files = Counter(file_of[n] for n in decls)
pillar = lambda f: ("core" if "/Core/" in f else
                    "sj" if "RouteMSJ" in f else "routem" if "RouteM" in f else
                    "deepest" if "Deepest" in f or "/D1" in f else
                    "headline" if "Headline" in f else "other")
cone_pillar = Counter(pillar(file_of[n]) for n in cone)

incone_fanin = Counter({n: len(rev[n] & cone) for n in cone if rev[n] & cone})

out = {"headlines": HEADLINES, "cone_size": len(cone),
       "cone_files": len(cone_files), "total_files": len(all_files),
       "cone": sorted(cone)}
(D / "cone.json").write_text(json.dumps(out, indent=1))

S = ["# Structure summary (from decls.json)", "",
     f"- decls: {len(decls)}; dependency edges: {sum(len(v) for v in deps.values())}",
     f"- headline roots: {len(HEADLINES)} ({', '.join(h.split('.')[-1] for h in HEADLINES)})",
     "",
     "## The cone (what the headlines actually stand on)",
     f"- **{len(cone)} decls ({100*len(cone)/len(decls):.0f}%) across "
     f"{len(cone_files)} files (of {len(all_files)})**",
     f"- by pillar: {dict(cone_pillar.most_common())}",
     f"- sorry-decls in tree: {len(sorries)}; **sorry-decls ON the cone: {len(sorry_in_cone)}**"
     + (f"  ⚠ {sorry_in_cone[:5]}" if sorry_in_cone else "  ✓ headline value-path sorry-free"),
     "",
     "## De-facto API (top 20 by fan-in, whole tree)", ""]
S += [f"- {fan_in[n]:>4} ← `{n.split('.')[-1]}`  ({file_of[n].split('/')[-1]})"
      for n, _ in fan_in.most_common(20)]
S += ["", "## Load-bearing on-cone theorems (top 15 by in-cone fan-in)", ""]
S += [f"- {incone_fanin[n]:>4} ← `{n.split('.')[-1]}`  ({file_of[n].split('/')[-1]})"
      for n, _ in incone_fanin.most_common(15) if decls[n]["kind"] == "theorem"][:15]
S += ["", "## Dead weight",
      f"- theorem orphans (no dependents in tree): {len(thm_orphans)} "
      f"({100*len(thm_orphans)/max(1,sum(1 for d in decls.values() if d['kind']=='theorem')):.0f}% of theorems)",
      f"- files with ZERO cone membership: {len(set(all_files)-set(cone_files))} "
      f"of {len(all_files)} (candidates: superseded scaffolding)", ""]
(D / "structure_summary.md").write_text("\n".join(S) + "\n")
print("\n".join(S[:26]))
