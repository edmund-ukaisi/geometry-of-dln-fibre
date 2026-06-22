#!/usr/bin/env python3
"""
verify_orthogonality_route.py — how to prove the ONE classical q-fact S3 needs:
    ORTH(u):  sum_{k=0}^{u} (-1)^k q^{C(k,2)} P_k P_{u-k} = [u==0].
Candidate Lean proofs (pick the cleanest), each verified exactly here.

ROUTE A — telescoping / Euler's pentagonal-free finite recursion.
  Multiply (x;q)_inf * 1/(x;q)_inf = 1 read at x^u.  In Lean we do NOT have
  infinite products; instead ORTH(u) for fixed u is a FINITE identity in q-series.
  The cleanest finite recursion: define the partial alternating sum and use
  P_succ : P(s+1) = P s * geomFactor(s+1)  and  geomFactor_mul_one_sub :
  geomFactor k * (1 - X^k) = 1.  We test the q-Pascal / contiguous recursion
  that drives an induction on u.

ROUTE B — q-binomial theorem coefficient form (the named identity), via a
  *finite* q-Pascal recurrence for [u choose k]_q.  Heavier (needs Gaussian
  binomials as objects).  We test whether ORTH reduces to a q-Pascal identity.

We check the recurrences that an induction-on-u proof would lean on:
  (R1) the "geometric-factor difference" identity that lets P_k absorb a (1-q^k):
       P_k - P_{k-1} = q^k P_k     (since P_k = P_{k-1} * 1/(1-q^k)  =>
       P_k (1-q^k) = P_{k-1}  =>  P_k - P_{k-1} = q^k P_k).  EXACT, drives telescope.
  (R2) Euler's identity coefficient recurrence for ORTH via splitting last factor.
"""
import sympy as sp
from verify_s3 import q, P, altP, DEG, Cbin2

def cap(poly, deg=DEG):
    p = poly if isinstance(poly, sp.Poly) else sp.Poly(sp.expand(poly), q)
    return sp.Poly({m: c for m, c in p.terms() if m[0] <= deg}, q)

def eqp(a, b, deg=DEG-2):
    return sp.expand(cap(a, deg).as_expr() - cap(b, deg).as_expr()) == 0

if __name__ == '__main__':
    # (R1) P_k * (1-q^k) = P_{k-1}, equivalently P_k - P_{k-1} = q^k P_k
    print("(R1) P_k (1-q^k) = P_{k-1}   and   P_k - P_{k-1} = q^k P_k:")
    r1 = True
    for k in range(1, 13):
        a = cap(P(k).as_expr()*(1-q**k))
        if not eqp(a, P(k-1)):
            r1 = False; print(f"  k={k}: FAIL (P_k(1-q^k)=P_{{k-1}})")
        b = cap(P(k).as_expr() - P(k-1).as_expr())
        c = cap((q**k)*P(k).as_expr())
        if not eqp(b, c):
            r1 = False; print(f"  k={k}: FAIL (P_k-P_{{k-1}}=q^k P_k)")
    print(f"  => {'PASS' if r1 else 'FAIL'}\n")

    # ORTH via the EULER finite recursion.  The slick proof: define
    #   S_u := sum_{k=0}^{u} altP(k) P(u-k).
    # We exhibit the contiguous recurrence that gives S_u=0 (u>=1) by induction.
    # Known (Euler): the alternating sum telescopes because
    #   altP(k) = (-1)^k q^{C(k,2)} P_k  satisfies altP(k) = altP(k-1) * (-q^{k-1}) * (geomFactor k extracted).
    # Cleanest verified recurrence between consecutive ORTH partial structures:
    #   The generating identity   prod_{i>=1}(1-x q^i) * prod_{i>=1} 1/(1-x q^i) = 1
    # truncated at x^u is exactly ORTH(u).  We confirm ORTH(u)=0 (u>=1) and that
    # the q-Pascal contiguous relation holds for the building block.
    print("ORTH(u) = sum_{k=0}^u altP(k) P(u-k) = [u=0]:")
    ok = True
    for u in range(0, 14):
        S = sp.Poly(sp.Integer(0), q)
        for k in range(0, u+1):
            S = cap(S + cap(altP(k).as_expr()*P(u-k).as_expr()))
        tgt = 1 if u == 0 else 0
        if not eqp(S, tgt):
            ok = False; print(f"  u={u}: FAIL value")
    print(f"  => {'PASS' if ok else 'FAIL'}\n")

    # The induction driver actually usable in Lean WITHOUT a q-binomial library:
    #   View 1/(x;q)_inf = sum_s P_s x^s and (x;q)_inf = sum_s altP(s) x^s as
    #   FINITE truncations T_n(x) = sum_{s=0}^n (..) x^s in (q-series)[x]/(x^{n+1}).
    #   Their product's x^u coeff (u<=n) = ORTH(u). Provable by: both are the
    #   x-power-series inverse of each other because
    #     (sum altP(s) x^s) * (1/(x;q)_inf)  read as a recursion on x-degree,
    #   and the closed alt form is forced by the SAME orthogonality => circular.
    # The NON-CIRCULAR finite proof = Cauchy/q-binomial theorem:
    #   1/(x;q)_inf = sum P_s x^s   is  q-binomial thm (Andrews 10.2.2),
    #   provable finitely by induction on the number of factors with the q-Pascal
    #   recurrence P_s = P_{s-1}/(1-q^s).  We verify the FACTOR-PEEL recursion that
    #   an induction on the truncation depth would use:
    #     sum_{s=0}^n P_s x^s  *  (1 - x q^{n+1})  ~  sum_{s=0}^n P_s^{(n)} x^s  shape.
    # Simpler: verify the *Euler* finite recurrence  e_u := altP(u):
    #   e_u + q^u * (shifted)  -- we test the concrete 2-term recurrence for ORTH:
    print("Euler 2-term driver:  altP(k) = -q^{k-1} * altP(k-1) * (1-q^k)/(1)  building block:")
    eok = True
    for k in range(1, 13):
        # altP(k) = (-1)^k q^{C(k,2)} P_k ;  altP(k-1)=(-1)^{k-1} q^{C(k-1,2)} P_{k-1}
        # ratio altP(k)/altP(k-1) = -q^{C(k,2)-C(k-1,2)} P_k/P_{k-1} = -q^{k-1} /(1-q^k)
        lhs = cap(altP(k).as_expr()*(1-q**k))
        rhs = cap((-(q**(k-1))) * altP(k-1).as_expr())
        if not eqp(lhs, rhs):
            eok = False; print(f"  k={k}: FAIL  (C(k,2)-C(k-1,2)={Cbin2(k)-Cbin2(k-1)} should be k-1={k-1})")
    print(f"  => {'PASS' if eok else 'FAIL'}")
    print("\nNOTE: altP(k)(1-q^k) = -q^{k-1} altP(k-1) is the EXACT 2-term recurrence")
    print("an induction-on-u proof of ORTH would use (no Gaussian binomial object).")
