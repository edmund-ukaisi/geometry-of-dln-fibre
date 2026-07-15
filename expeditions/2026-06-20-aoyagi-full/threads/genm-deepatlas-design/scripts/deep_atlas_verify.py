"""
Deep-resolution atlas verification (exact).
Deep chain widths (v0,...,vp) = (M2,...,Mlast); Z_deep = L0·L1·...·L_{p-1}, Li: v_i x v_{i+1}.
Target {rank Z_deep <= s}, s = rho - k, rho = min widths.
"""
from functools import lru_cache
from itertools import product as iproduct
import numpy as np
from fractions import Fraction

@lru_cache(maxsize=None)
def CR(widths, s):
    v = tuple(widths)
    if len(v) == 2:
        v0, v1 = v
        if s >= min(v0, v1): return 0
        return (v0 - s) * (v1 - s)
    vpm1, vp = v[-2], v[-1]
    best = None
    for r in range(0, min(vpm1, vp) + 1):
        outer = (vpm1 - r) * (vp - r)
        inner = 0 if r <= s else CR(v[:-2] + (r,), s)
        val = outer + inner
        if best is None or val < best: best = val
    return best

# ---- Q1: single-bottleneck sufficiency ----
# "single bottleneck at layer j, rank <= s there": codim = det-codim of forcing layer j (as v_j x v_{j+1})
#   BUT going through: if bottleneck is the composite up to layer j having rank <= s.
# Simplest hypothesis: CR = min over "single layer i made rank <= s" where that layer is v_i x v_{i+1}:
#   codim to make Z rank<=s via layer i bottleneck = (v_i - s)*(v_{i+1} - s)  [make that ONE layer rank<=s]
#   but only valid if s <= min(v_i,v_{i+1}); if s>=min, that layer costs 0.
def single_bottleneck(widths, s):
    p = len(widths)-1
    best = None
    for i in range(p):  # layer i: v_i x v_{i+1}
        vi, vj = widths[i], widths[i+1]
        c = max(0, vi-s)*max(0, vj-s) if s < min(vi,vj) else 0
        if best is None or c < best: best = c
    return best

print("=== Q1: is CR = single-layer-bottleneck (make ONE layer rank<=s)? ===")
mismatch1 = 0
for p in range(1,4):
  for widths in iproduct(range(1,7), repeat=p+1):
    rho = min(widths)
    for s in range(0, rho):
        a = CR(widths, s); b = single_bottleneck(widths, s)
        if a != b:
            mismatch1 += 1
            if mismatch1 <= 12:
                print(f"  widths={widths} s={s}: CR={a} single-bottleneck={b}")
print("total single-bottleneck mismatches:", mismatch1)
