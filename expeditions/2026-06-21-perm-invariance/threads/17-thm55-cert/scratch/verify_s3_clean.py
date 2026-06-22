#!/usr/bin/env python3
"""
verify_s3_clean.py — the CLEANEST Lean realization of S3, and which inductive
shape it wants.  The question: can S3 (inversion) be a per-vector algebraic
identity provable by induction on n=min d, WITHOUT setting up a linear system
of (n+1) vectors?

Candidate (DIRECT SUBSTITUTION + ORTHOGONALITY):
  Claim T(d):  Q^0_d = sum_{s=0}^{min d} altP(s) * Pmult(d-s),  altP(s)=(-1)^s q^{C(s,2)} P_s.
  Substitute S2  Pmult(e) = sum_{t=0}^{min e} P_t Q^0_{e-t}  into the RHS, e=d-s:
    RHS = sum_{s=0}^{n} altP(s) * sum_{t=0}^{min(d-s)} P_t Q^0_{d-s-t}
        = sum over (s,t) altP(s) P_t Q^0_{d-s-t}.
  Reindex by u=s+t (u=0..n) and inner k=s (0..u):  Q^0_{d-u} weight
    W_u = sum_{k=0}^{u} altP(k) P(u-k) = [u==0]   (orthogonality!).
  So RHS = Q^0_{d-0} * 1 = Q^0_d.   DONE — no linear system, just S2 + orthogonality.

CAVEAT to check: the inner upper limit is min(d-s), not n-s. We need the
double sum to be exactly over { (s,t) : s>=0, t>=0, s+t <= n } so the reindex
to u=s+t in [0,n] and orthogonality apply cleanly.  Two facts to confirm
EXACTLY:
  (i)  For s in [0,n], the terms of S2 for e=d-s with t > n-s VANISH or are
       harmless when collected by u=s+t > n.  Actually min(d-s) = n-s exactly
       (since min d = n and subtracting s lowers every coord by s, so the min is
       n-s), so the inner limit IS n-s, t in [0,n-s], hence s+t in [0,n]. CLEAN.
  (ii) Orthogonality sum_{k=0}^u altP(k) P(u-k) = [u=0] for u=0..n.

We verify the whole DIRECT-SUBSTITUTION identity numerically AND confirm
min(d-s) = n-s, so the Lean target is:
  T(d) follows from  S2  +  orthogonality  +  the reindex {s+t=u},
NO induction on a vector-system, NO infinite (x;q)_inf.
"""
import sympy as sp
from verify_s3 import q, P, Pmult, altP, Qseries_def, DEG, eq_upto, Cbin2

def cap(poly, deg=DEG):
    p = poly if isinstance(poly, sp.Poly) else sp.Poly(sp.expand(poly), q)
    return sp.Poly({m: c for m, c in p.terms() if m[0] <= deg}, q)

def vsub(dvec, t):
    return [d - t for d in dvec]

if __name__ == '__main__':
    tests = [
        (2,2,2), (2,3,2), (2,2,3), (2,4,2),
        (1,2,3), (3,2,1), (2,1,2),
        (3,3,3), (1,2,2,3), (3,2,2,1), (4,4,4),
    ]

    # (i) min(d-s) = (min d) - s  for s in [0, min d]
    print("(i) min(d-s) == min(d) - s  for all s in [0, min d]:")
    iok = True
    for dvec in tests:
        n = min(dvec)
        for s in range(0, n+1):
            if min(vsub(list(dvec), s)) != n - s:
                iok = False
                print(f"  d={dvec} s={s}: {min(vsub(list(dvec),s))} != {n-s}")
    print(f"  => {'PASS' if iok else 'FAIL'}\n")

    # (ii) orthogonality already PASS in verify_s3; reconfirm to n.
    print("(ii) orthogonality sum_{k=0}^u altP(k) P(u-k) = [u=0]:")
    ook = True
    for u in range(0, 13):
        acc = sp.Poly(sp.Integer(0), q)
        for k in range(0, u+1):
            acc = cap(acc + cap(altP(k).as_expr()*P(u-k).as_expr()))
        tgt = sp.Poly(sp.Integer(1) if u == 0 else sp.Integer(0), q)
        if sp.expand(acc.as_expr()-tgt.as_expr()) != 0:
            ook = False
            print(f"  u={u}: FAIL")
    print(f"  => {'PASS' if ook else 'FAIL'}\n")

    # (iii) THE DIRECT-SUBSTITUTION identity:
    #   sum_{s=0}^{n} altP(s) * [ sum_{t=0}^{n-s} P_t Q^0_{d-s-t} ]  ==  Q^0_d
    print("(iii) direct-substitution: sum_{s} altP(s) (sum_t P_t Q^0_{d-s-t}) == Q^0_d:")
    diok = True
    for dvec in tests:
        n = min(dvec)
        acc = sp.Poly(sp.Integer(0), q)
        for s in range(0, n+1):
            inner = sp.Poly(sp.Integer(0), q)
            for t in range(0, n-s+1):
                inner = cap(inner + cap(P(t).as_expr()*Qseries_def(vsub(list(dvec), s+t), 0).as_expr()))
            acc = cap(acc + cap(altP(s).as_expr()*inner.as_expr()))
        ok = eq_upto(acc, Qseries_def(list(dvec), 0), DEG-6)
        diok = diok and ok
        if not ok:
            print(f"  d={dvec}: MISMATCH")
    print(f"  => {'PASS' if diok else 'FAIL'}\n")

    # (iv) AND the reindex-collected form: weight of Q^0_{d-u} is [u=0]
    #   sum_{u=0}^{n} (sum_{k=0}^{u} altP(k) P(u-k)) Q^0_{d-u}  ==  Q^0_d
    print("(iv) reindexed (u=s+t): sum_u (sum_k altP(k)P(u-k)) Q^0_{d-u} == Q^0_d:")
    rok = True
    for dvec in tests:
        n = min(dvec)
        acc = sp.Poly(sp.Integer(0), q)
        for u in range(0, n+1):
            w = sp.Poly(sp.Integer(0), q)
            for k in range(0, u+1):
                w = cap(w + cap(altP(k).as_expr()*P(u-k).as_expr()))
            acc = cap(acc + cap(w.as_expr()*Qseries_def(vsub(list(dvec), u), 0).as_expr()))
        ok = eq_upto(acc, Qseries_def(list(dvec), 0), DEG-6)
        rok = rok and ok
        if not ok:
            print(f"  d={dvec}: MISMATCH")
    print(f"  => {'PASS' if rok else 'FAIL'}")
