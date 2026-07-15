#!/usr/bin/env python3
# guards: incidence-estimate
# config: M=(2,2,3); binding corner T1 = minAdm/2; additive split ab/2 + reduced
# provenance: threads/genm-incidencepp/incidence-cert.md
"""Consistency guard for the (∗_T1) incidence estimate at its binding corner.

At M=(2,2,3) the terminal threshold is T1 = minAdm([2,2,3])/2 = 2. The incidence
estimate splits it additively as ab/2 + reduced-threshold = 0.5 + minAdm([1,3])/2
= 0.5 + 1.5 = 2. Exit 0 (survives) iff the split matches T1 exactly (sharp)."""
import sys

from _minadm import minAdm

T1 = minAdm((2, 2, 3)) / 2          # 2.0
split = 0.5 + minAdm((1, 3)) / 2    # 0.5 + 1.5 = 2.0
consistent = (T1 == split)
print(f"T1 = {T1}  additive split ab/2 + minAdm([1,3])/2 = {split}  sharp={consistent}")
sys.exit(0 if consistent else 1)
