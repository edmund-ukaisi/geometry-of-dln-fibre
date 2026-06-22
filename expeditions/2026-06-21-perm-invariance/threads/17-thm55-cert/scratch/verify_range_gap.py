#!/usr/bin/env python3
"""
verify_range_gap.py — the LANDED fivegon sums r over range(d_0+1) [r=0..d_0],
but the paper's eqn:key sums s over 0..min d.  Pin that the gap terms vanish:
    Qseries d r = 0  for  min d < r <= d_0,
so  sum_{r=0}^{d_0} Qseries d r = sum_{r=0}^{min d} Qseries d r,  and S2 (eqn:key)
gets the correct upper limit min d.

REASON: kostantPartitions d r requires a corner m_{0,N}=r and Kostant constraints
d_k = sum_{i<=k<=j} m_{ij} >= m_{0,N} = r  for every k (since (0,N) covers every k).
So r <= min_k d_k = min d; for r>min d the set is EMPTY, Qseries=0.

We confirm:
  (i)  Qseries_def(d,r) == 0 for min d < r <= d_0.
  (ii) sum_{r=0}^{d_0} Qseries_def(d,r) == sum_{r=0}^{min d} Qseries_def(d,r) == Pmult(d).
"""
import sympy as sp
from verify_s3 import q, Pmult, Qseries_def, DEG, eq_upto, kostant_partitions

def cap(poly, deg=DEG):
    p = poly if isinstance(poly, sp.Poly) else sp.Poly(sp.expand(poly), q)
    return sp.Poly({m: c for m, c in p.terms() if m[0] <= deg}, q)

if __name__ == '__main__':
    # pick d where d_0 > min d (so the gap is nonempty)
    tests = [(3,1,2), (3,2,1), (4,2,2), (2,1,2), (3,1,1,2), (4,4,2,3)]
    print("(i) Qseries_def(d,r) == 0 for min d < r <= d_0  (gap terms vanish):")
    iok = True
    for d in tests:
        d0, mind = d[0], min(d)
        for r in range(mind+1, d0+1):
            # also confirm the kostant set is empty
            empty = (len(list(kostant_partitions(list(d), r))) == 0)
            qz = (Qseries_def(list(d), r).as_expr() == 0)
            if not (empty and qz):
                iok = False
                print(f"  d={d} r={r}: empty={empty} Qseries0={qz}")
    print(f"  => {'PASS' if iok else 'FAIL'}\n")

    print("(ii) sum_{r=0}^{d_0} = sum_{r=0}^{min d} = Pmult(d):")
    iiok = True
    for d in tests:
        d0, mind = d[0], min(d)
        s_full = sp.Poly(sp.Integer(0), q)
        for r in range(0, d0+1):
            s_full = cap(s_full + cap(Qseries_def(list(d), r)))
        s_min = sp.Poly(sp.Integer(0), q)
        for r in range(0, mind+1):
            s_min = cap(s_min + cap(Qseries_def(list(d), r)))
        ok = eq_upto(s_full, s_min, DEG-6) and eq_upto(s_full, Pmult(list(d)), DEG-6)
        iiok = iiok and ok
        if not ok:
            print(f"  d={d}: MISMATCH")
    print(f"  => {'PASS' if iiok else 'FAIL'}")
