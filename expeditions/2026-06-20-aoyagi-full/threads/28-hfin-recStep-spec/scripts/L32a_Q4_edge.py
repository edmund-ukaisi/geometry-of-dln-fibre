#!/usr/bin/env python3
"""
L32a_Q4_edge.py — scrutinise the det M11 → 0 edge (the sharpest risk in DESIGN CHOICE 2). On a
(r−1)-minor-pivot cell, is the shear M21·M11⁻¹ ACTUALLY bounded by the argmax-over-minors condition, or
can it blow up where det M11 is small (R approaching rank r−2)?

EXACT worst-case construction (r=3, k=2): pick R with |R_kl| ≤ 1, find a 2×2 minor that is the MAX |det|
among all 2×2 minors, and check whether M21·M11⁻¹ (the 1×2 shear row) can be large there.
"""
import sympy as sp
import numpy as np
from itertools import combinations

# Symbolic: M11 a 2x2 with det = d, entries bounded by 1. M21 a 1x2 row, entries bounded by 1.
# shear = M21 · M11⁻¹ = M21 · adj(M11)/det(M11). adj(M11) entries are ±(entries of M11) ⟹ |adj entries| ≤ 1.
# So |shear| ~ |M21|·|adj M11| / |det M11| ≤ 2/|det M11|.  This BLOWS UP as det M11 → 0.  CONFIRM the risk.
print("="*78)
print(" THE RISK: shear M21·M11⁻¹ = M21·adj(M11)/det(M11) ~ O(1)/det(M11) → ∞ as det M11 → 0.")
print("="*78)
print("So the naive 'shear ≤ 1' claim is WRONG inside a cell where det M11 is small. Need to check:")
print("does the ARGMAX-over-2×2-minors condition prevent det M11 from being small RELATIVE to ‖R‖?")
print()

# Numerical hunt: random R with |entries|≤1, pick the max-|det| 2×2 minor, compute the shear norm.
rng = np.random.default_rng(0)
r, k = 3, 2
maxshear = 0.0; worst = None
for _ in range(200000):
    R = rng.uniform(-1, 1, (r, r))
    # all 2x2 minors (row-pair, col-pair)
    best = None; bestdet = -1
    for I in combinations(range(r), k):
        for J in combinations(range(r), k):
            M = R[np.ix_(I, J)]
            dd = abs(np.linalg.det(M))
            if dd > bestdet:
                bestdet = dd; best = (I, J, M)
    if best is None or bestdet < 1e-12:
        continue
    I, J, M11 = best
    Irest = [i for i in range(r) if i not in I]
    Jrest = [j for j in range(r) if j not in J]
    M21 = R[np.ix_(Irest, J)]   # (r-k) x k
    shear = M21 @ np.linalg.inv(M11)
    sn = np.linalg.norm(shear, ord=2)
    if sn > maxshear:
        maxshear = sn; worst = (R.copy(), bestdet, sn)
print(f"max shear ‖M21·M11⁻¹‖₂ over 200k random R (|entries|≤1), max-det 2×2 minor pivot: {maxshear:.4f}")
print(f"  worst det M11 = {worst[1]:.4f}, shear = {worst[2]:.4f}")
print()
print("INTERPRETATION:")
if maxshear < 100:
    print(f"  The shear stays BOUNDED (≤ ~{maxshear:.1f}) — the max-minor-pivot condition DOES control it.")
    print("  WHY: if det M11 is small but M11 is the MAX 2×2 minor, then ALL 2×2 minors are small ⟹ R is")
    print("  near rank ≤ 1 ⟹ M21 is also small (the rows are near-dependent), so M21·M11⁻¹ = (small)/(small)")
    print("  stays O(1). The argmax balances numerator and denominator. (Heuristic — verify symbolically.)")
else:
    print(f"  The shear can be LARGE (≥ {maxshear:.1f}) — the cell needs FURTHER subdivision. Q4 NEEDS-CARE.")
print()

# Symbolic sanity on the cleanest sub-case (r=2,k=1): shear = R10/R00, cell {|R00| = max |entry|}.
print("="*78)
print(" SYMBOLIC r=2,k=1: shear = R10/R00 on cell {|R00| ≥ |R10|,|R01|,|R11|}")
print("="*78)
print("  |R00| is the MAX entry ⟹ |R10| ≤ |R00| ⟹ |shear| = |R10/R00| ≤ 1. BOUNDED, absolute. ✓")
print("  (This is the corank-1 case = the (3,3,4) anchor's inner. The shear IS ≤ 1 here — clean.)")
print()

# The honest general statement: for k = r−1 (one corank drop), the max (r−1)-minor M11 and the shear.
print("="*78)
print(" THE HONEST GENERAL STATEMENT (the fix if needed)")
print("="*78)
print("For ONE-corank descent (k = r−1, the residual Sc is 1×1), the worst shear over the max-(r−1)-minor")
print("cell is bounded by an absolute constant C(r) (numerics: r=3 gives ~", f"{maxshear:.1f}). The")
print("mechanism: the max minor being the LARGEST means the cell is a genuine 'this minor dominates'")
print("region where the shear coefficients (Cramer ratios of sub-minors) are bounded. This is the")
print("classical fact that a max-pivot LU/Gauss step has bounded multipliers. If C(r) grows with r, the")
print("comparison CONSTANT grows but stays FINITE per (r,p) — which is ALL the upper bound needs (the")
print("threshold is preserved by ANY finite two-sided comparison, the constant need not be ≤ 1).")
