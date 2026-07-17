#!/usr/bin/env python3
"""HUNT h11 -- (2,2,2,2) ANGULAR family (Codex Q1/Q3 gap): the non-toroidal incidence
relation h = 1 + a1*b2 = 0 (rank-1 row dir of C1 annihilates rank-1 col dir of C2).

On a1 != 0 introduce h as a coordinate: b2 = (h-1)/a1. The product entries and the
Jacobian become RATIONAL in the new coords (al1,a1,b1,d1,al2,a2,h,d2,p,q,r,s); the
valuation of a rational N/D is wdeg(N) - wdeg(D). We search all monomial weights and
also explicitly the Codex center Z=(al1,al2,d1,d2,p,q,r,s,h) with a1,b2 units. KILL iff
2*rho < minAdm = 3. This closes scope caveat (i) for the (2,2,2,2) angular divisors.
"""
import sys, itertools
from fractions import Fraction as F
import sympy as sp
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm

al1, a1, b1, d1 = sp.symbols("al1 a1 b1 d1")
al2, a2, d2, h = sp.symbols("al2 a2 d2 h")
p, q, r, s = sp.symbols("p q r s")
newvars = [al1, a1, b1, d1, al2, a2, h, d2, p, q, r, s]

b2 = (h - 1) / a1                                    # angular coordinate: h = 1 + a1*b2
M1 = sp.Matrix([[al1, al1 * a1], [al1 * b1, al1 * (a1 * b1 + d1)]])
M2 = sp.Matrix([[al2, al2 * a2], [al2 * b2, al2 * (a2 * b2 + d2)]])
C3 = sp.Matrix([[p - a2 * r, q - a2 * s], [r, s]])   # same shear as h6

old_exprs = [M1[0, 0], M1[0, 1], M1[1, 0], M1[1, 1],
             M2[0, 0], M2[0, 1], M2[1, 0], M2[1, 1],
             C3[0, 0], C3[0, 1], C3[1, 0], C3[1, 1]]
Jmat = sp.Matrix([[sp.diff(e, v) for v in newvars] for e in old_exprs])
Jdet = sp.simplify(Jmat.det())
P = sp.expand(sp.simplify(M1 * M2 * C3))
gens = [sp.together(P[i, j]) for i in range(2) for j in range(2)]


def _supp(e):
    e = sp.expand(e)
    if e == 0:
        return None
    return [tuple(int(x) for x in m) for m in sp.Poly(e, *newvars).monoms()]


def _numden_supp(expr):
    """(numerator exps, denominator exps) of a rational expr over newvars."""
    num, den = sp.fraction(sp.together(sp.expand(expr)))
    return _supp(num), _supp(den)


# precompute supports ONCE
GEN_SUPP = [_numden_supp(g) for g in gens]
JAC_SUPP = _numden_supp(Jdet)


def _wd(exps, w):
    return min(sum(e[i] * w[i] for i in range(len(w))) for e in exps)


def _val(numden, w):
    ns, ds = numden
    if ns is None:
        return None
    vn = _wd(ns, w)
    vd = _wd(ds, w) if ds is not None else 0
    return vn - vd


def two_rho(w):
    denom = None
    for nd in GEN_SUPP:
        v = _val(nd, w)
        if v is None:
            continue
        denom = v if denom is None else min(denom, v)
    if denom is None or denom <= 0:
        return None
    num = sum(w) + _val(JAC_SUPP, w)
    return F(num, denom)


if __name__ == "__main__":
    ma = minAdm((2, 2, 2, 2))
    print("=== (2,2,2,2) ANGULAR chart (h = 1 + a1*b2 as coordinate) ===")
    print("Jacobian det =", Jdet)
    print("gens:")
    for g in gens:
        print("   ", g)
    # explicit Codex center Z: weight 1 on al1,al2,d1,d2,p,q,r,s,h ; 0 on a1,b1,a2
    wz = {al1: 1, a1: 0, b1: 0, d1: 1, al2: 1, a2: 0, h: 1, d2: 1, p: 1, q: 1, r: 1, s: 1}
    w = [wz[v] for v in newvars]
    print(f"\nCodex center Z: 2rho = {two_rho(w)} (expect 15/4)")
    # exhaustive small-weight search
    best = None; argw = None; hits = []
    for wt in itertools.product(range(3), repeat=len(newvars)):
        if sum(wt) == 0:
            continue
        val = two_rho(list(wt))
        if val is None:
            continue
        if best is None or val < best:
            best, argw = val, wt
        if val < ma:
            hits.append((val, wt))
    print(f"\nexhaustive {{0,1,2}}^12 angular search: min 2rho = {best} (rho={best/2}); minAdm={ma}")
    print(f"  argmin w = {dict(zip([str(v) for v in newvars], argw))}")
    print(f"  UNDERSHOOTS (<{ma}): {len(hits)}")
    for val, wt in hits[:6]:
        print(f"    2rho={val} at {wt}  <== KILL CANDIDATE")
    print("  VERDICT:", "SURVIVE (angular family, this chart)" if not hits else "KILL FOUND")
