#!/usr/bin/env python3
"""
verify_orth_shift.py — is relation (II)  altP(u)+T(u) = -f_{u-1}  provable by a
clean index-shift using (AA): altP(k)(1-X^k) = -X^{k-1} altP(k-1)?  If so, ORTH
has a fully self-contained single-induction Lean proof with NO second variable
and NO Gaussian binomial.

T(u) = sum_{k=0}^{u-1} altP(k) X^{u-k} P(u-k).
Goal:  altP(u) + T(u) = -f_{u-1} = -sum_{j=0}^{u-1} altP(j) P(u-1-j).

Approach 1 (symmetric Euler): use (AA) on the SECOND-variable-free form.  We test
the alternative decomposition obtained by applying (PA) the OTHER way, then
matching.  Rather than re-derive, we ALSO test the SYMMETRIC partner identity:
  apply (PA) to factor P(u-k) AND (AA) to altP(k) and look for the telescoping
  that maps f_u to a single boundary term.

The cleanest KNOWN finite proof of  sum_k (-1)^k q^{C(k,2)} P_k P_{u-k}=[u=0] is:
  it is the coefficient form of  ( (x;q)_inf )( 1/(x;q)_inf ) = 1, and the finite
  truncation of  1/(x;q)_inf = sum_s P_s x^s  is the q-binomial theorem, proved by
  induction on the number of factors via P_succ.  We instead test a PURELY q-side
  recurrence to confirm there exists a 2-term-recurrence single induction:

We measure  R(u) := altP(u) + T(u) + f_{u-1}   (should be 0 by (II)) and ALSO try
to express R(u) via (AA)-shifted T:  define
  T'(u) := sum_{k=1}^{u} (-X^{k-1} altP(k-1)) * [P(u-k)/(1-X^k)]   -- needs division, skip.
Cleaner: verify the COMBINED identity that an induction can use directly:
  (C)  f_u * 1 = (k=u boundary) + sum_{k=0}^{u-1} altP(k) P(u-k),
       and  P(u-k) = P(u-1-k) + X^{u-k}P(u-k)  [PA],  so the FIRST part is f_{u-1}.
  Hence  f_u = f_{u-1} + altP(u) + X^u * U(u)   where U(u)=sum_{k=0}^{u-1} altP(k) X^{-k}... NO.
  Keep:   f_u - f_{u-1} = altP(u) + T(u).   [that's (I), PROVED]
  So the WHOLE content is showing  altP(u)+T(u)=0 for u>=1 when f_{u-1}=0 fails (we saw
  it is 0 only for u>=2 under IH; for u=1 it's -1=-f_0). So the induction is:
     f_0 = 1; for u>=1, f_u = f_{u-1} + altP(u)+T(u);
     and  altP(u)+T(u) = -f_{u-1}  (II) is the lemma => f_u=0 for u>=1, f_u=f_{u-1} for the carry.
  But (II) STILL references f_{u-1}.  So (II) is NOT a free recurrence; it is equivalent
  to ORTH. => the (PA)-expansion ALONE does not close the induction; we need a SECOND
  independent relation (the (AA) shift) to pin altP(u)+T(u) without f_{u-1}.

We TEST the (AA)-shifted form of T(u):  apply (AA) to write altP(k) = -X^{-(k-1)} altP(k+1)/(1-X^{k+1})... messy.
Instead test the DIRECT symmetric identity that IS a clean recurrence:
  (S)  sum_{k=0}^{u} altP(k) P(u-k)  ==  sum_{k=0}^{u} altP(u-k) P(k)   (symmetry, trivial reindex),
  and the q-binomial-theorem-free proof via the EULER pentagonal recursion does need
  the truncated 2nd variable.  CONCLUSION TEST: confirm the truncated-Y route is the
  minimal self-contained one by re-verifying it is provable by induction on truncation:
  define  fac_n(Y) = prod_{k=1}^{n} 1/(1-Y q^k)-truncated ... we test the q-binomial
  theorem finite form:   prod_{k=1}^{n}(1 - Y q^k)^{-1} = sum_{s>=0} P_s^{(n)} Y^s
  where P_s^{(n)} -> P_s as n->inf; for the ORTH at order u we only need n=u.
"""
import sympy as sp
from verify_s3 import q, P, altP, DEG

def cap(poly, deg=DEG):
    p = poly if isinstance(poly, sp.Poly) else sp.Poly(sp.expand(poly), q)
    return sp.Poly({m: c for m, c in p.terms() if m[0] <= deg}, q)
def E(poly, deg=DEG-2):
    return cap(poly, deg).as_expr()
def iszero(poly, deg=DEG-3):
    return sp.expand(E(poly, deg)) == 0

# The clean q-binomial theorem (finite, single 2nd variable Y, induction on # factors):
#   define G_n(Y) = sum_{s=0}^{S} P_s Y^s truncated; claim G_inf = prod 1/(1-Y q^k).
# ORTH(u) = coeff of Y^u in  (sum_s altP(s) Y^s)(sum_s P_s Y^s).
# We verify the q-binomial theorem identity that PROVES the convolution-inverse:
#   ( sum_{s} altP(s) Y^s )  ==  ( sum_{s} P(s) Y^s )^{-1}  in (qseries)[[Y]].
# Equivalent finite statement, provable by induction on M (truncation in Y):
#   B_M(Y) := sum_{s=0}^{M} altP(s) Y^s,  A_M(Y) := sum_{s=0}^{M} P(s) Y^s,
#   then A_M(Y) B_M(Y) = 1 + O(Y^{M+1}).  We verify A_M B_M ≡ 1 mod Y^{M+1}.
if __name__ == '__main__':
    Y = sp.symbols('Y')
    MMAX = 13
    print("q-binomial-theorem convolution inverse (truncated in Y):")
    print("  A_M(Y)=sum_{s<=M} P(s) Y^s,  B_M(Y)=sum_{s<=M} altP(s) Y^s,  A_M B_M ≡ 1 mod Y^{M+1}:")
    ok = True
    for M in range(0, MMAX+1):
        A = sum(E(P(s).as_expr())*Y**s for s in range(0, M+1))
        B = sum(E(altP(s).as_expr())*Y**s for s in range(0, M+1))
        prod = sp.expand(A*B)
        # reduce mod Y^{M+1}
        red = sum((prod.coeff(Y, j))*Y**j for j in range(0, M+1))
        # each coeff is a q-series; cap and check: coeff Y^0 =1, Y^j=0 for 1<=j<=M
        good = (sp.expand(E(red.coeff(Y,0)) - 1) == 0)
        for j in range(1, M+1):
            if sp.expand(E(red.coeff(Y, j))) != 0:
                good = False
        if not good:
            ok = False; print(f"  M={M}: FAIL")
    print(f"  => {'PASS' if ok else 'FAIL'}")
    print()
    print("The induction that proves A_inf B_inf = 1 in (qseries)[[Y]] (hence ORTH at every order):")
    print("  A_inf(Y) = prod_{k>=1} 1/(1-Y q^k)? NO -- A_inf(Y)=sum P_s Y^s is the q-binomial thm")
    print("  1/(Y;q)_inf-with-shift. The minimal Lean target: A and B are mutual inverses in the")
    print("  Y-adic PowerSeries ring (qseries)⟦Y⟧, proved by showing their product's Y-coeffs are")
    print("  [n=0]. That product coeff IS ORTH(n). So ORTH <=> 'B = A^{-1} in (qseries)⟦Y⟧'.")
    print("  PROVING it: the q-binomial theorem  sum_s P_s Y^s = prod_{k>=1}(1-Yq^{k-1})^{-1}? ")
    print("  -- in Lean cleanest as: A satisfies the functional eqn A(Y)(1-Y) ... q-difference.")
