#!/usr/bin/env python3
"""HUNT h6 -- (2,2,2,2) [L=3] composed DOUBLE-incidence chart + weighted-divisor hunt.

This is the L>=3 gate: the paper's coverage direction is assertion-level for L>=3,
so an untracked sub-1/2-minAdm divisor, if any, lives here. We build a genuine
composition of TWO incidence blow-ups (on C1 and C2) plus row-contraction shears on
C3 that expose the product-vanishing conditions as coordinates, then search monomial
weights EXHAUSTIVELY. Jacobian computed exactly by sympy (expect ~ al1^3 al2^3).

KILL iff any weight gives 2*rho = (sum w + w(Jac)) / min_g w(g o phi) < minAdm = 3.
"""
import sys, itertools
from fractions import Fraction as F
import sympy as sp
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm

# incidence coords for C1 and C2 (2x2 each), pivot (0,0)
al1, a1, b1, d1 = sp.symbols("al1 a1 b1 d1")
al2, a2, b2, d2 = sp.symbols("al2 a2 b2 d2")
# C3 sheared: expose [1,*]-contraction. Keep 4 free coords.
p, q, r, s = sp.symbols("p q r s")     # C3 entries (sheared below)

M1 = sp.Matrix([[al1, al1 * a1], [al1 * b1, al1 * (a1 * b1 + d1)]])
M2 = sp.Matrix([[al2, al2 * a2], [al2 * b2, al2 * (a2 * b2 + d2)]])
# shear C3 so that row0 absorbs a2-contraction: C3 = [[p - a2*r, q - a2*s],[r, s]]
C3 = sp.Matrix([[p - a2 * r, q - a2 * s], [r, s]])

newvars = [al1, a1, b1, d1, al2, a2, b2, d2, p, q, r, s]
# old entries: C1(4), C2(4), C3(4) in terms of new
oldC1 = [M1[0, 0], M1[0, 1], M1[1, 0], M1[1, 1]]
oldC2 = [M2[0, 0], M2[0, 1], M2[1, 0], M2[1, 1]]
oldC3 = [C3[0, 0], C3[0, 1], C3[1, 0], C3[1, 1]]
old_exprs = oldC1 + oldC2 + oldC3

Jmat = sp.Matrix([[sp.diff(e, v) for v in newvars] for e in old_exprs])
Jdet = sp.expand(Jmat.det())

P = sp.expand(M1 * M2 * C3)
gens = [sp.expand(P[i, j]) for i in range(2) for j in range(2)]


def support(expr):
    expr = sp.expand(expr)
    if expr == 0:
        return []
    return [tuple(int(e) for e in m) for m in sp.Poly(expr, *newvars).monoms()]


gen_sup = [support(g) for g in gens]
jac_sup = support(Jdet)


def wdeg(sup, w):
    return min(sum(e * wi for e, wi in zip(m, w)) for m in sup)


def hunt(wmax):
    best = None; argw = None; hits = []
    nv = len(newvars)
    for w in itertools.product(range(wmax + 1), repeat=nv):
        sw = sum(w)
        if sw == 0:
            continue
        denom = min(wdeg(sig, w) for sig in gen_sup)
        if denom <= 0:
            continue
        num = sw + wdeg(jac_sup, w)
        rr = F(num, denom)
        if best is None or rr < best:
            best, argw = rr, w
        if rr < minAdm((2, 2, 2, 2)):
            hits.append((rr, w))
    return best, argw, hits


if __name__ == "__main__":
    ma = minAdm((2, 2, 2, 2))
    print("=== (2,2,2,2) composed double-incidence chart ===")
    print("Jacobian det =", Jdet)
    print("generators:")
    for g in gens:
        print("   ", g)
    print(f"minAdm={ma}, target rho=3/2 (2*rho=3)\n")
    for wmax in (2, 3):
        best, argw, hits = hunt(wmax)
        print(f"[wmax={wmax}] min 2*rho={best} (rho={best/2}); undershoots(<{ma})={len(hits)}")
        print(f"          argmin w={dict(zip([str(v) for v in newvars], argw))}")
        for (rr, w) in hits[:8]:
            print(f"          2rho={rr} at {w}  <== KILL CANDIDATE")
        print("          VERDICT:", "SURVIVE" if not hits else "KILL FOUND")
