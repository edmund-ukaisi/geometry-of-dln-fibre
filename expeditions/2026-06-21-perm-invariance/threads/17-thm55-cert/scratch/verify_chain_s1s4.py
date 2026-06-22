#!/usr/bin/env python3
"""
verify_chain_s1s4.py — the S1, S2, and S3-FINITE-RECURSION steps, exact.

S1 (shift, Lemma 5.7, r=s form used downstream):
    Q^0_{d-s} = (q)_s * Q^s_d ,   where (q)_s = (1-q)(1-q^2)...(1-q^s).
    [paper's Lemma 5.7 with r=s, r->s, s->s: Q_{d-s}^{0} = prod_{k=1}^{s}(1-q^k) Q_d^s]
    NOTE the Lean-friendly reading: P_s * Q^0_{d-s} = Q^s_d * P_s * (q)_s,
    but (q)_s * P_s = 1, so:  P_s * Q^0_{d-s}  via S1 is NOT how we want it.
    We use the form needed by S2: P_s * Q^0_{d-s} appears in eqn:key.

S2 (eqn:key):
    Pmult(d) = sum_{s=0}^{min d} P_s * Q^0_{d-s}.
    [derived from 5gon  Pmult(d) = sum_s Q^s_d  and S1: Q^s_d = (q)_s^{-1} Q^0_{d-s}
     = P_s Q^0_{d-s}  since (q)_s^{-1}=P_s.]

S3 (the inversion, FINITE form):
    Treat n := min d.  Define for k=0..n:
       A_k := Pmult(d - (n-k)) = Pmult shifted so that A_n = Pmult(d), A_0 = Pmult(d-n).
       B_k := Q^0_{d-(n-k)}.
    Then S2 for the vectors d, d-1, ..., d-n reads (lower-triangular, unit diagonal P_0=1):
       A_k = sum_{j=0}^{k} P_j * B_{k-j}     (k = 0..n)
    The CLOSED inverse (b_n = top) is:
       B_n = sum_{s=0}^{n} (-1)^s q^{C(s,2)} P_s * A_{n-s}
           = sum_{s=0}^{n} (-1)^s q^{C(s,2)} P_s * Pmult(d-s),
    which is exactly Q^0_d = Thm5.5 RHS at r=0.
    This is FINITE: only the (n+1)x(n+1) triangular system, invertible by the
    orthogonality  sum_k altP(k) P(m-k) = [m=0].  NO infinite (x;q)_inf needed.

We verify:
  (a) S1 (r=s form):  Q^0_{d-s} == (q)_s * Q^s_d.
  (b) S2 (eqn:key):   Pmult(d) == sum_{s=0}^{min d} P_s * Q^0_{d-s}.
  (c) S3 finite-recursion forward:  A_k == sum_{j=0}^k P_j B_{k-j}, all k.
  (d) S3 finite-inversion:          B_n == sum_s altP(s) A_{n-s}  (= Thm5.5 r=0).
"""
import sympy as sp
from verify_s3 import (q, P, Pmult, altP, Qseries_def, DEG, eq_upto, Cbin2)

def qpoch(s):
    """(q)_s = prod_{k=1}^s (1-q^k)."""
    expr = sp.Integer(1)
    for k in range(1, s+1):
        expr = sp.expand(expr * (1 - q**k))
    return sp.Poly(expr, q)

def cap(poly, deg=DEG):
    p = poly if isinstance(poly, sp.Poly) else sp.Poly(sp.expand(poly), q)
    return sp.Poly({m: c for m, c in p.terms() if m[0] <= deg}, q)

def vsub(dvec, t):
    return [d - t for d in dvec]

if __name__ == '__main__':
    tests = [
        (2,2,2), (2,3,2), (2,2,3), (2,4,2),
        (1,2,3), (3,2,1), (2,1,2),
        (3,3,3), (1,2,2,3), (3,2,2,1),
    ]

    # (a) S1
    print("S1 (shift, r=s form):  Q^0_{d-s} == (q)_s * Q^s_d")
    a_ok = True
    for dvec in tests:
        mind = min(dvec)
        for s in range(0, mind+1):
            lhs = Qseries_def(vsub(list(dvec), s), 0)
            rhs = cap(qpoch(s) * Qseries_def(list(dvec), s).as_expr())
            ok = eq_upto(lhs, rhs, DEG-6)
            a_ok = a_ok and ok
            if not ok:
                print(f"  d={dvec} s={s}: MISMATCH")
    print(f"  => {'PASS' if a_ok else 'FAIL'}\n")

    # (b) S2 eqn:key
    print("S2 (eqn:key):  Pmult(d) == sum_{s=0}^{min d} P_s * Q^0_{d-s}")
    b_ok = True
    for dvec in tests:
        mind = min(dvec)
        acc = sp.Poly(sp.Integer(0), q)
        for s in range(0, mind+1):
            term = cap(P(s).as_expr() * Qseries_def(vsub(list(dvec), s), 0).as_expr())
            acc = cap(acc + term)
        ok = eq_upto(Pmult(list(dvec)), acc, DEG-6)
        b_ok = b_ok and ok
        if not ok:
            print(f"  d={dvec}: MISMATCH")
    print(f"  => {'PASS' if b_ok else 'FAIL'}\n")

    # (c) + (d) S3 finite triangular system + inversion
    print("S3 finite-recursion forward (A_k = sum_j P_j B_{k-j}) and inversion (B_n = sum_s altP(s) A_{n-s}):")
    c_ok = True
    d_ok = True
    for dvec in tests:
        n = min(dvec)
        A = [Pmult(vsub(list(dvec), n-k)) for k in range(0, n+1)]
        B = [Qseries_def(vsub(list(dvec), n-k), 0) for k in range(0, n+1)]
        # forward
        for k in range(0, n+1):
            acc = sp.Poly(sp.Integer(0), q)
            for j in range(0, k+1):
                acc = cap(acc + cap(P(j).as_expr()*B[k-j].as_expr()))
            if not eq_upto(A[k], acc, DEG-6):
                c_ok = False
                print(f"  fwd d={dvec} k={k}: MISMATCH")
        # inversion: B_n
        acc = sp.Poly(sp.Integer(0), q)
        for s in range(0, n+1):
            acc = cap(acc + cap(altP(s).as_expr()*A[n-s].as_expr()))
        if not eq_upto(B[n], acc, DEG-6):
            d_ok = False
            print(f"  inv d={dvec}: MISMATCH")
    print(f"  forward => {'PASS' if c_ok else 'FAIL'}")
    print(f"  inversion => {'PASS' if d_ok else 'FAIL'}")
