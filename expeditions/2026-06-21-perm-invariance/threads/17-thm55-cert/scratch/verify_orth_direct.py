#!/usr/bin/env python3
"""
verify_orth_direct.py — find the cleanest SINGLE-VARIABLE induction for
    f_u := sum_{k=0}^{u} altP(k) P(u-k) = [u==0]      (altP(k)=(-1)^k X^{C(k,2)} P_k)

We test the EULER finite recurrence that proves f_u=0 (u>=1) directly,
using only (PA) P(j)=P(j-1)+X^j P(j) i.e. P(j)(1-X^j)=P(j-1), and
(AA) altP(k)(1-X^k) = -X^{k-1} altP(k-1).

Derivation to verify (the textbook q-binomial-theorem telescoping, single var):
  Consider  (1-X^u) f_u.  Use (PA) on the factor... but u-k varies.  Better:
  Pull the (1-X^?) through altP via (AA).  Standard trick: weight each term by
  (1-X^k) and use altP(k)(1-X^k)=-X^{k-1}altP(k-1) to shift index k->k-1.

  Define  S := sum_{k=0}^{u} altP(k) P(u-k).
  Apply (PA) to P(u-k) when u-k>=1:  P(u-k) = P(u-k-1) + X^{u-k} P(u-k).  Then
    S = altP(u) P_0
        + sum_{k=0}^{u-1} altP(k) [P(u-1-k) + X^{u-k} P(u-k)]
      = [ sum_{k=0}^{u-1} altP(k) P(u-1-k) ]                 = f_{u-1}
        + altP(u)                                            (k=u term, P_0=1)
        + sum_{k=0}^{u-1} altP(k) X^{u-k} P(u-k).
  So:  f_u = f_{u-1} + altP(u) + X^u sum_{k=0}^{u-1} altP(k) X^{-k} P(u-k)  -- X^{-k} bad.
  Keep X^{u-k} intact:  T := sum_{k=0}^{u-1} altP(k) X^{u-k} P(u-k).
  We verify the EXACT relation  f_u - f_{u-1} - altP(u) - T == 0   (identity, all u).
  Then SEPARATELY verify that altP(u) + T telescopes to -f_{u-1} (so f_u=0 for u>=1):
    test  altP(u) + T + f_{u-1} == f_u, AND  f_u==0 => altP(u)+T = -f_{u-1}.
  The real driver: show  altP(u) + T = -f_{u-1}  directly (this is what makes f_u=0).
  We verify  altP(u) + T == -f_{u-1}   exactly (u>=1).  If TRUE, then
    f_u = f_{u-1} + (altP(u)+T) = f_{u-1} - f_{u-1} = 0.   Clean single induction.
"""
import sympy as sp
from verify_s3 import q, P, altP, DEG, Cbin2

def cap(poly, deg=DEG):
    p = poly if isinstance(poly, sp.Poly) else sp.Poly(sp.expand(poly), q)
    return sp.Poly({m: c for m, c in p.terms() if m[0] <= deg}, q)
def E(poly, deg=DEG-2):
    return cap(poly, deg).as_expr()
def iszero(poly, deg=DEG-3):
    return sp.expand(E(poly, deg)) == 0

def f(u):
    acc = sp.Integer(0)
    for k in range(0, u+1):
        acc = E(acc + E(altP(k).as_expr()*P(u-k).as_expr()))
    return acc

def T(u):
    acc = sp.Integer(0)
    for k in range(0, u):  # k=0..u-1
        acc = E(acc + E(altP(k).as_expr()*(q**(u-k))*P(u-k).as_expr()))
    return acc

if __name__ == '__main__':
    UMAX = 13
    # decomposition identity (always true, just (PA) expansion):
    print("(I) decomposition: f_u == f_{u-1} + altP(u) + T(u)  (u>=1):")
    iok = True
    for u in range(1, UMAX+1):
        if not iszero(E(f(u)) - E(f(u-1)) - E(altP(u).as_expr()) - E(T(u))):
            iok = False; print(f"  u={u}: FAIL")
    print(f"  => {'PASS' if iok else 'FAIL'}\n")

    # the telescoping driver:
    print("(II) telescoping driver:  altP(u) + T(u) == -f_{u-1}  (u>=1):")
    iiok = True
    for u in range(1, UMAX+1):
        if not iszero(E(altP(u).as_expr()) + E(T(u)) + E(f(u-1))):
            iiok = False; print(f"  u={u}: FAIL  altP(u)+T(u)+f(u-1)={sp.expand(E(altP(u).as_expr())+E(T(u))+E(f(u-1)))}")
    print(f"  => {'PASS' if iiok else 'FAIL'}\n")

    # Hmm: (II) requires knowing f_{u-1}.  For the INDUCTION we may assume f_{u-1}=0
    # (u-1>=1) so altP(u)+T(u)=0; base u=1 needs altP(1)+T(1)=-f_0=-1.  Test the
    # SPLIT the induction actually uses:
    print("(III) what the induction uses:")
    print("   u=1 base region:  altP(1)+T(1) == -f_0 == -1 :", iszero(E(altP(1).as_expr())+E(T(1))+1))
    print("   u>=2, ASSUMING f_{u-1}=0:  altP(u)+T(u) == 0 :")
    iiiok = True
    for u in range(2, UMAX+1):
        # under IH f_{u-1}=0, (II) says altP(u)+T(u) should be 0
        if not iszero(E(altP(u).as_expr()) + E(T(u))):
            iiiok = False; print(f"     u={u}: altP(u)+T(u) = {sp.expand(E(altP(u).as_expr())+E(T(u)))} (NONZERO; the recurrence is NOT a pure 2-term)")
    print(f"   => {'altP(u)+T(u)=0 for u>=2 (PURE telescope, induction works)' if iiiok else 'NOT pure: altP(u)+T(u) carries f_{u-1} (so (II) is the genuine relation; induction still closes via (I)+(II) but T mixes orders)'}")
    print()
    print("CONCLUSION: relation (I) is the exact (PA)-expansion; (II) altP(u)+T(u)=-f_{u-1}")
    print("is the genuine telescoping that, with (I), gives f_u=0 by induction. Check which")
    print("of (II)/(III) is the clean Lean target.")
