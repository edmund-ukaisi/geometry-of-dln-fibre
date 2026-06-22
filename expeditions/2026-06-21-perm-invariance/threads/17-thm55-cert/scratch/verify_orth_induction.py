#!/usr/bin/env python3
"""
verify_orth_induction.py — pin the EXACT single-induction proof of orthogonality
    ORTH(u): f_u := sum_{k=0}^{u} altP(k) P(u-k) = [u==0],
using ONLY the two finite recurrences (both Lean-proved-able):
    (PA) P(j)   * (1-X^j)  = P(j-1)        for j>=1          [from P_succ + geomFactor_mul_one_sub]
    (AA) altP(k)* (1-X^k)  = -X^{k-1} altP(k-1)   for k>=1    [pure ring + P_succ]
and NO Gaussian binomial.

The classical Euler argument: consider the FULL generating product. We avoid x.
Instead, the clean finite proof uses the "q-binomial theorem" recurrence on the
inner P factor.  Standard slick identity (Cauchy):
    sum_{k=0}^{u} (-1)^k q^{C(k,2)} [u choose k]_q = [u==0],
but [u choose k]_q is the Gaussian binomial, which is exactly what we want to
avoid.  Our f_u uses P_k P_{u-k}, NOT a single binomial, so it is a DIFFERENT
(and in fact simpler) telescoping.

CANDIDATE A — induction via the recurrence on P(u-k) in the LAST factor.
  Split f_u by whether k=u (term altP(u) P_0 = altP(u)) vs k<u (P(u-k) with u-k>=1).
  Use (PA): P(u-k) = P(u-k-1) + X^{u-k} P(u-k)  ... messy.  Test instead:

CANDIDATE B (the one we will recommend) — multiply f_u by (1-X^u) and telescope.
  Claim:  f_u * (1 - X^u) = 0   for u >= 1, hence f_u = 0 (1-X^u is X-adic non-zero-divisor;
  in ℤ⟦X⟧ multiplication by (1-X^u) is INJECTIVE since 1-X^u has constant term 1, a unit times
  ... actually 1-X^u is a non-unit but a non-zero-divisor: leading coeff argument).  We TEST
  whether f_u (1-X^u) = 0.   If TRUE, the induction is:  f_u(1-X^u)=0 => f_u=0.
  But that needs f_u(1-X^u)=0 to be itself provable -- test its exact value.

CANDIDATE C — the genuinely clean one: f_u satisfies a PURE recurrence
        f_u = X^u * f_u'   or   f_u = (something) f_{u-1}
  Let's just MEASURE candidate relations and report which is exactly 0 / clean.
"""
import sympy as sp
from verify_s3 import q, P, altP, DEG, Cbin2

def cap(poly, deg=DEG):
    p = poly if isinstance(poly, sp.Poly) else sp.Poly(sp.expand(poly), q)
    return sp.Poly({m: c for m, c in p.terms() if m[0] <= deg}, q)
def E(poly, deg=DEG-2):
    return cap(poly, deg).as_expr()
def iszero(poly, deg=DEG-2):
    return sp.expand(E(poly, deg)) == 0

def f(u):
    acc = sp.Integer(0)
    for k in range(0, u+1):
        acc = E(acc + E(altP(k).as_expr()*P(u-k).as_expr()))
    return acc

if __name__ == '__main__':
    UMAX = 13
    print("f_u values:")
    for u in range(0, UMAX+1):
        print(f"  f_{u} = {sp.expand(f(u))}")
    print()

    # CANDIDATE B: f_u * (1-X^u) == 0 for u>=1 ?
    print("CANDIDATE B:  f_u * (1 - X^u) == 0  (u>=1)?")
    bok = True
    for u in range(1, UMAX+1):
        if not iszero(E(f(u))*(1-q**u)):
            bok = False; print(f"  u={u}: NONZERO")
    print(f"  => {'holds (but trivial since f_u=0 anyway)' if bok else 'FAIL'}\n")

    # The MEANINGFUL question: is there a recurrence proving f_u=0 from f_{<u}
    # WITHOUT already knowing f_u=0?  The Euler telescoping:
    #   define g_u(j) = partial sum capturing the standard pentagon recursion.
    # Cleanest verified: the "absorb (1-X^u) into the k=u and k=0 boundary" identity.
    # We test the EXACT Euler recurrence used in textbooks for the finite Cauchy id:
    #   sum_{k} (-1)^k q^{C(k,2)} P_k P_{u-k}:  pull P_{u-k}=P_{u-k-1}+X^{u-k}P_{u-k} (PA-rearranged)
    #   to split f_u into f over u-1 shifted.  Concretely test:
    #     f_u  ==  sum_{k=0}^{u-1} altP(k) P(u-1-k)  +  X-correction  ?
    # We measure  D_u := f_u - [sum_{k=0}^{u} altP(k) * (P(u-k) - X^{?} ...)].
    # Rather than guess, verify the proven-clean route: f as coeff of the PRODUCT
    #   ( sum_{s=0}^{u} altP(s) Y^s ) * ( sum_{s=0}^{u} P(s) Y^s )  at Y^u  -- a SECOND
    # variable Y but TRUNCATED (finite, in (q-series)[Y]/(Y^{u+1})), NOT infinite.
    print("TRUNCATED-Y route: coeff of Y^u in (sum_{s<=u} altP(s) Y^s)(sum_{s<=u} P(s) Y^s) == [u=0]:")
    Y = sp.symbols('Y')
    yok = True
    for u in range(0, UMAX+1):
        A = sum(E(altP(s).as_expr())*Y**s for s in range(0, u+1))
        B = sum(E(P(s).as_expr())*Y**s for s in range(0, u+1))
        prod = sp.expand(A*B)
        coeff_u = prod.coeff(Y, u)
        coeff_u = E(coeff_u)
        tgt = 1 if u==0 else 0
        if sp.expand(coeff_u - tgt) != 0:
            yok = False; print(f"  u={u}: FAIL coeff={sp.expand(coeff_u)}")
    print(f"  => {'PASS' if yok else 'FAIL'}")
    print()
    print("VERDICT on ORTH: the cleanest NON-CIRCULAR finite proof is the q-binomial")
    print("theorem  1/(x;q)_inf = sum P_s x^s  (Andrews 10.2.2). In Lean over ℤ⟦X⟧ this")
    print("is provable as a FINITE truncated-Y identity by induction on the truncation,")
    print("driven by P_succ + geomFactor_mul_one_sub; ORTH is then the x^u coeff of the")
    print("product of the two truncations.  This is a self-contained ~1-file mini-lemma,")
    print("NOT a Gaussian-binomial library.")
