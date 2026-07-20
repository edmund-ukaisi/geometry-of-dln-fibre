#!/usr/bin/env python3
# guards: coverage-theorem, resolution-tree
# provenance: threads/15-psi-adjudication (pnp-psi). T1: is the Case-1 u-pivot chart (1(1))
#   geometrically load-bearing in the per-node cover? Aoyagi pp.15-16: Case-1 center =
#   {d-block} ∪ {u_{s,k}}, d_center = J1*(M^{(S+1)}-J)+1 (the "+1" is u). Chart 1(1) pivots on u
#   (d_ij = u*d'_ij); charts 1(2) pivot on d-entries. Exact rational — NO Monte-Carlo.
#
# THE QUESTION (T1): does the u-pivot chart cover points that NO d-pivot chart reaches?
#   Concretely the u-max-modulus sector {|d_ij| <= |u| forall ij}, in particular the u-axis
#   {d-block = 0, u != 0}. If YES, the u-pivot is NOT a "ledger-only extra" (tick-162 (i)).
#
# Model: center coords = (d_1,...,d_{D}, u) with D = J1*(cols-J) d-entries + 1 divisor u.
#   pivot-i chart covers point x iff coord i is a max-modulus coord of x (and if x_i=0, all=0).
#   This is exactly Engine/PivotCover's max-modulus domain (transcribed from the Lean STATEMENT,
#   cross-checked vs leg1-leg4-pivot-tiling.py preimage_in_dom).
from fractions import Fraction as F
from itertools import product
import sys

def pivot_covers(i, x):
    """Does the pivot-i max-modulus chart cover point x? (x_i is a max-modulus coord.)"""
    if x[i] == 0:
        return all(xk == 0 for xk in x)      # pivot 0 forces all 0
    return all(abs(x[k]) <= abs(x[i]) for k in range(len(x)))

def run():
    fails = []
    report = []
    # Case-1 nodes: d-block sizes (J1 rows) x (cols) plus 1 u-divisor. u is the LAST coord index.
    # d_center = J1*cols + 1.
    for (J1, cols) in [(1,1),(1,2),(2,1),(2,2),(1,3),(3,1),(2,3),(3,2)]:
        Dd = J1*cols            # number of d-entries
        d_center = Dd + 1       # + u
        u_idx = d_center - 1     # u is the last coordinate
        d_idxs = list(range(Dd))

        # (a) the u-AXIS {all d = 0, u != 0}: covered by u-pivot, missed by every d-pivot.
        axis = tuple(F(0) if k != u_idx else F(1,2) for k in range(d_center))
        u_covers_axis   = pivot_covers(u_idx, axis)
        d_covers_axis   = any(pivot_covers(i, axis) for i in d_idxs)
        if not u_covers_axis:  fails.append(("u-pivot fails to cover u-axis", J1, cols))
        if d_covers_axis:      fails.append(("some d-pivot wrongly covers u-axis", J1, cols))

        # (b) the STRICT-INTERIOR u-max sector (positive measure): |d_ij| < |u|, u!=0.
        #     take every d = +/- u/3 : all strictly < |u|. Covered only by u-pivot.
        interior = tuple((F(1,3) if (k % 2 == 0) else F(-1,3)) if k != u_idx else F(1)
                         for k in range(d_center))
        u_covers_int = pivot_covers(u_idx, interior)
        d_covers_int = any(pivot_covers(i, interior) for i in d_idxs)
        if not u_covers_int: fails.append(("u-pivot fails strict-interior u-max", J1, cols))
        if d_covers_int:     fails.append(("d-pivot wrongly covers strict-interior u-max", J1, cols))

        # (c) DROP the u-pivot: does the d-pivot-only family (tick-162 (i) escape) leave a gap?
        #     Exact grid: enumerate cube points; find any missed by the d-only family.
        st = 4 if d_center <= 3 else (3 if d_center <= 5 else 2)
        vals = [F(-1) + F(2,st)*s for s in range(st+1)]
        d_only_miss = None
        for x in product(vals, repeat=d_center):
            if not any(pivot_covers(i, x) for i in d_idxs):   # no d-pivot covers x
                # confirm the FULL family (with u) does cover it -> genuine undershoot of d-only
                if any(pivot_covers(i, x) for i in range(d_center)):
                    d_only_miss = x
                    break
        if d_only_miss is None and d_center >= 2:
            fails.append(("d-only family had NO gap (u-pivot redundant?)", J1, cols))
        report.append((J1, cols, d_center, u_covers_axis, d_covers_axis,
                       u_covers_int, d_covers_int, d_only_miss is not None))
    return fails, report

if __name__ == "__main__":
    fails, report = run()
    print("T1 — is the Case-1 u-pivot chart load-bearing? (exact rational)")
    print(" J1 cols d_ctr | u-cov-axis d-cov-axis | u-cov-int d-cov-int | d-only-gap-exists")
    for (J1,cols,dc,uca,dca,uci,dci,gap) in report:
        print(f"  {J1}   {cols}    {dc}   |    {uca!s:5}     {dca!s:5}   |   {uci!s:5}    {dci!s:5}   |    {gap}")
    print()
    if fails:
        print("FAIL:", fails[:8]); sys.exit(1)
    print("PASS: u-pivot uniquely covers the u-max sector (axis + strict interior);")
    print("      every d-pivot MISSES it; the d-only family (tick-162 (i)) leaves a real gap.")
    print("  => T1 = YES: the u-pivot chart is geometrically load-bearing, NOT a ledger-only extra.")
    sys.exit(0)
