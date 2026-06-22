#!/usr/bin/env python3
"""
verify_m6.py — the M6 (Cor 5.10) closing from Thm 5.5.

Thm 5.5 (proved by M4):  Qseries d r = P_r * sum_{s=0}^{min d - r} altP(s) Pmult(d-r-s),
   where Pmult(d-r-s) = prod_i P(d_i - r - s)  is manifestly symmetric in the multiset of d.

M6 target (per r):   Qseries (d∘σ) r = Qseries d r   for every permutation σ of Fin(n+1).
Then via the LANDED M5 bridge (cCodim_eq_of_Qseries_eq / numTop_eq_of_Qseries_eq):
   cCodim (d∘σ) r = cCodim d r   and   numTop (d∘σ) r = numTop d r.   = Cor 5.10.

CHECKS:
 (A) RHS of Thm5.5 is permutation-invariant: every factor P_r, altP(s), and
     Pmult(d-r-s) is invariant; only Pmult(d-r-s) depends on d, via prod_i P(d_i-r-s),
     which is the LANDED Pmult_sub_comp_perm with c=r+s.
 (B) min(d∘σ) = min d, so the sum RANGE  s=0..min d - r  is the SAME for d and d∘σ
     (the range is multiset-data only). This is the r-range subtlety: the upper limit
     min d - r is a multiset invariant, so both sides have identical summation ranges.
 (C) hence Qseries(d∘σ) r = Qseries d r for ALL r in [0, min d] (where Thm5.5 applies),
     AND for r > min d both sides are 0 (empty kostantPartitions) -- so the per-r identity
     holds for ALL r, and the M5 bridge needs nonemptiness which holds iff r <= min d.
 (D) Directly confirm Qseries(d∘σ) r == Qseries d r on the Kostant DEFINITION (not via 5.5),
     for all perms and all r -- this is the ground truth the chain must reproduce.
"""
import sympy as sp
import itertools as it
from verify_s3 import q, P, Pmult, altP, Qseries_def, DEG, eq_upto

def cap(poly, deg=DEG):
    p = poly if isinstance(poly, sp.Poly) else sp.Poly(sp.expand(poly), q)
    return sp.Poly({m: c for m, c in p.terms() if m[0] <= deg}, q)

def thm55(dvec, r):
    mind = min(dvec)
    acc = sp.Poly(sp.Integer(0), q)
    for s in range(0, mind - r + 1):
        shifted = [d - r - s for d in dvec]
        if any(x < 0 for x in shifted):
            continue
        term = cap(altP(s).as_expr()*Pmult(shifted).as_expr())
        acc = cap(acc + term)
    return cap(P(r).as_expr()*acc.as_expr())

if __name__ == '__main__':
    bases = [(2,2,3), (1,2,3), (2,4,2), (1,2,2,3), (3,2,2,1)]

    print("(D) GROUND TRUTH: Qseries_def(d∘σ, r) == Qseries_def(d, r) for all perms, all r<=min:")
    dok = True
    for base in bases:
        for perm in set(it.permutations(base)):
            for r in range(0, min(base)+1):
                if not eq_upto(Qseries_def(list(perm), r), Qseries_def(list(base), r), DEG-6):
                    dok = False; print(f"  base={base} perm={perm} r={r}: MISMATCH")
    print(f"  => {'PASS' if dok else 'FAIL'}\n")

    print("(A)+(C) Thm5.5 RHS is perm-invariant and matches Qseries_def, all r:")
    aok = True
    for base in bases:
        for perm in set(it.permutations(base)):
            for r in range(0, min(base)+1):
                lhs = thm55(list(perm), r)
                rhs = thm55(list(base), r)
                if not eq_upto(lhs, rhs, DEG-6):
                    aok = False; print(f"  RHS not invariant: base={base} perm={perm} r={r}")
                # and RHS == def
                if not eq_upto(thm55(list(base), r), Qseries_def(list(base), r), DEG-6):
                    aok = False; print(f"  RHS != def: base={base} r={r}")
    print(f"  => {'PASS' if aok else 'FAIL'}\n")

    print("(B) range invariance: min(d∘σ) == min(d):")
    bok = True
    for base in bases:
        if any(min(perm) != min(base) for perm in set(it.permutations(base))):
            bok = False
    print(f"  => {'PASS (range min d - r is a multiset invariant)' if bok else 'FAIL'}\n")

    print("(C') r > min d: both Qseries d r and Qseries(d∘σ) r are 0 (empty kostant):")
    cok = True
    for base in bases:
        r = min(base)+1
        if Qseries_def(list(base), r).as_expr() != 0:
            cok = False
        for perm in set(it.permutations(base)):
            if Qseries_def(list(perm), r).as_expr() != 0:
                cok = False
    print(f"  => {'PASS (per-r identity holds vacuously for r>min d)' if cok else 'FAIL'}")
