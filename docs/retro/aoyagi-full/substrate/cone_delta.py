#!/usr/bin/env python3
"""Mint-day cone delta: cone_before_mint.json (frozen baseline, conditional-
headline era) vs the freshly regenerated cone.json (post-mint walker run).

Run AFTER: lb DLNFibre at the minted tip → WalkDecls → graph_readouts.py.
Add the minted unsuffixed headline to graph_readouts.HEADLINES first (it will
be picked up automatically if named aoyagi_learning_coefficient*).
"""
from __future__ import annotations
import json
from collections import Counter
from pathlib import Path

D = Path(__file__).resolve().parent
before = json.loads((D / "cone_before_mint.json").read_text())
after = json.loads((D / "cone.json").read_text())
B, A = set(before["cone"]), set(after["cone"])

pillar = lambda n: ("sj-descent" if ".RouteMSJ" in n or "Decorated" in n or "PivotDom" in n
                    or "PivotFin" in n or "HeadSplit" in n else
                    "routem" if "RouteM" in n else
                    "deepest-d1" if "Deepest" in n or ".D1" in n else "other")
gained, lost = A - B, B - A
S = ["# Cone delta — the mint as a structural event", "",
     f"- before (conditional headline): {len(B)} decls / {before['cone_files']} files",
     f"- after  (minted headline):      {len(A)} decls / {after['cone_files']} files",
     f"- GAINED {len(gained)} decls: {dict(Counter(pillar(n) for n in gained).most_common())}",
     f"- lost {len(lost)} (superseded arms falling out): "
     f"{dict(Counter(pillar(n) for n in lost).most_common(4))}",
     "",
     "The 'gained' row is the (□) discharge made visible: the descent machinery snapping",
     "into the load-bearing cone the moment the unconditional theorem consumes it.", ""]
(D / "cone_delta.md").write_text("\n".join(S))
print("\n".join(S))
