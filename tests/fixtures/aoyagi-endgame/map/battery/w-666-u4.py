#!/usr/bin/env python3
# kills: route-fullblock-deepfloor
# config: M=(6,6,6), claimed threshold (minAdm([4,6]) + (6-4)^2)/2 vs true minAdm/2
# provenance: threads/genm-routeverify/routeverify-cert.md
"""Refuter for the full-block deep-floor route.

The route's claimed threshold is (minAdm([4,6]) + (6-4)^2)/2 = 14, but the true
threshold is minAdm([6,6,6])/2 = 13.5. Since 13.5 < 14 the interval [13.5, 14)
holds divergent exponents the route would wrongly certify. Exit 1 (killed)."""
import sys

from _minadm import minAdm

claimed = (minAdm((4, 6)) + (6 - 4) ** 2) / 2   # 14.0
true_thr = minAdm((6, 6, 6)) / 2                 # 13.5
divergent = true_thr < claimed
print(f"claimed={claimed}  true={true_thr}  divergent_interval={divergent}")
sys.exit(1 if divergent else 0)
