#!/usr/bin/env python3
"""
verify_codex_orth.py — verify Codex's SINGLE-VARIABLE orthogonality induction,
the cleanest Lean route (no second variable, no Gaussian binomial).

O(u) := sum_{k=0}^u altP(k) P(u-k).
CLAIM (recurrence, u>=1):  O(u)*(1-X^u) = (1-X^{u-1}) * O(u-1).
RESTS ON the pure split (all u, all k<=u):
   1 - X^u = (1 - X^{u-k}) + X^{u-k}*(1 - X^k)
and the two coefficient recurrences:
   P_m (1-X^m) = P_{m-1}        (m>=1)
   altP_k(1-X^k) = -X^{k-1} altP_{k-1}   (k>=1)
=> with base O(0)=1, O(1)(1-X)=(1-X^0)O(0)=0, and induction O(u-1)=0 (u>=2):
   O(u)(1-X^u)=0, and geomFactor(u)*(1-X^u)=1 => O(u)=0.
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

def O(u):
    acc = sp.Integer(0)
    for k in range(0, u+1):
        acc = E(acc + E(altP(k).as_expr()*P(u-k).as_expr()))
    return acc

if __name__ == '__main__':
    UMAX = 13
    # the pure split identity (polynomial in q, exact)
    print("split:  1 - q^u == (1 - q^{u-k}) + q^{u-k}(1 - q^k)  for all 0<=k<=u:")
    sok = True
    for u in range(0, UMAX+1):
        for k in range(0, u+1):
            if sp.expand((1-q**u) - ((1-q**(u-k)) + q**(u-k)*(1-q**k))) != 0:
                sok = False; print(f"  u={u},k={k}: FAIL")
    print(f"  => {'PASS' if sok else 'FAIL'}\n")

    # the recurrence
    print("recurrence:  O(u)(1-q^u) == (1-q^{u-1}) O(u-1)   (u>=1):")
    rok = True
    for u in range(1, UMAX+1):
        lhs = E(E(O(u))*(1-q**u))
        rhs = E((1-q**(u-1))*E(O(u-1)))
        if not iszero(lhs - rhs):
            rok = False; print(f"  u={u}: FAIL")
    print(f"  => {'PASS' if rok else 'FAIL'}\n")

    # full conclusion O(u)=[u=0]
    print("conclusion O(u)=[u=0]:")
    cok = all((iszero(O(u)-1) if u==0 else iszero(O(u))) for u in range(0, UMAX+1))
    print(f"  => {'PASS' if cok else 'FAIL'}")
