#!/usr/bin/env python3
"""Cone-aware sorry accounting — the prototype for a `scripts/sorries` v2.

Classifies every sorry-tainted declaration (from decls.json kernel axioms) by
liveness relative to DECLARED ROOTS:
  LIVE-frontier — a root transitively depends on it (open obligation; must be
                  tracked, owned, and trending to zero),
  FOSSIL        — reachable from no root (dead scaffolding; pruning inventory,
                  harmless to the result but misleading to readers).
Adds age (pickaxe first-introduction date) per live item.

Roots = the headline theorems + the composition-skeleton spine (mint wrapper,
descent driver) — i.e. "the goal" in the goal-relative zero-sorry architecture.
"""
from __future__ import annotations
import json, subprocess
from collections import deque
from datetime import datetime, timezone
from pathlib import Path

D = Path(__file__).resolve().parent
REPO = D.parents[4]
doc = json.loads((D / "decls.json").read_text())
decls = {d["name"]: d for d in doc["decls"]}

ROOT_PATTERNS = ["aoyagi_learning_coefficient",           # all headline variants
                 "routeMBoxThresholdFinite_of_decoratedDescent",  # descent driver
                 "_gen_of_descent"]                        # mint wrapper
roots = [n for n in decls if any(p in n for p in ROOT_PATTERNS)]

deps = {n: [m for m in set(d.get("deps_proof", []) + d.get("deps_type", []))
            if m in decls] for n, d in decls.items()}
seen, q = set(roots), deque(roots)
while q:
    for m in deps.get(q.popleft(), []):
        if m not in seen:
            seen.add(m); q.append(m)

sorried = [n for n, d in decls.items()
           if any("sorry" in a.lower() for a in d.get("axioms", []))]
live = sorted(n for n in sorried if n in seen)
fossil = sorted(n for n in sorried if n not in seen)


def age_days(name: str):
    out = subprocess.run(["git", "log", "-S", name.split(".")[-1], "--format=%aI",
                          "413566b3..origin/expedition/aoyagi-full"],
                         cwd=REPO, text=True, stdout=subprocess.PIPE).stdout.split()
    if not out:
        return None
    born = datetime.fromisoformat(out[-1])
    return round((datetime.now(timezone.utc) - born).total_seconds() / 86400, 1)


S = ["# Frontier readout (cone-aware sorry accounting)", "",
     f"anchor: decls.json @ {doc.get('_meta', {}).get('generated', '?')} "
     f"(re-run walker at tip for current numbers)", "",
     f"- roots declared: {len(roots)} ({', '.join(r.split('.')[-1] for r in roots[:5])}…)"
     if len(roots) > 5 else f"- roots declared: {len(roots)} ({', '.join(r.split('.')[-1] for r in roots)})",
     f"- sorry-tainted decls: {len(sorried)} total → **LIVE-frontier {len(live)}**, fossil {len(fossil)}", ""]
if live:
    S += ["## LIVE frontier (open obligations — each needs an owner)", ""]
    S += [f"- `{n.split('.')[-1]}` ({decls[n]['file'].split('/')[-1]}) — age {age_days(n)}d"
          for n in live]
else:
    S += ["## LIVE frontier: EMPTY — every root is sorry-free (goal-relative zero-sorry holds)"]
S += ["", f"## Fossils ({len(fossil)}) — pruning inventory, off every root's cone", ""]
S += [f"- `{n.split('.')[-1]}` ({decls[n]['file'].split('/')[-1]})" for n in fossil[:30]]
(D / "frontier.md").write_text("\n".join(S) + "\n")
print("\n".join(S[:20]))
