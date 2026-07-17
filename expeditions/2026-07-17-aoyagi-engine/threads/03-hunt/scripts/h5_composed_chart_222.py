#!/usr/bin/env python3
"""HUNT h5 -- (2,2,2) FULL composed achiever chart + exhaustive weighted-divisor hunt.

Chart phi (new -> old), a genuine birational modification:
  C1 incidence at pivot (0,0):  C1 = alpha[[1,a],[b, ab+delta]]
  C2 shear exposing the C1C2=0 conditions g0,g1:
     C2_00 = g0 - a*c2_10,  C2_01 = g1 - a*c2_11,  C2_10 = c2_10,  C2_11 = c2_11
new coords y = (alpha,a,b,delta,g0,c2_10,g1,c2_11).

For a monomial weight w on y, the induced divisorial valuation has (exact)
   2*rho = ( sum w + w(det d old/d new) ) / min_g w(g o phi).
This chart is the one carrying the sharing structure (b, delta couple the residual),
so an EXHAUSTIVE weight search here probes Tier B3 (weighted centers) at the exact
locus the D3 cert flagged. KILL iff any weight gives 2*rho < minAdm = 3.
"""
import sys, itertools
from fractions import Fraction as F
import sympy as sp
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm

al, a, b, de = sp.symbols("al a b de")
g0, g1, c210, c211 = sp.symbols("g0 g1 c210 c211")
newvars = [al, a, b, de, g0, c210, g1, c211]

# old entries in terms of new
C1 = sp.Matrix([[al, al * a], [al * b, al * (a * b + de)]])
C2_00 = g0 - a * c210
C2_01 = g1 - a * c211
C2 = sp.Matrix([[C2_00, C2_01], [c210, c211]])
old_exprs = [C1[0, 0], C1[0, 1], C1[1, 0], C1[1, 1], C2[0, 0], C2[0, 1], C2[1, 0], C2[1, 1]]

# exact Jacobian of the composite map
Jmat = sp.Matrix([[sp.diff(e, v) for v in newvars] for e in old_exprs])
Jdet = sp.expand(Jmat.det())

# product generators in new coords
P = sp.expand(C1 * C2)
gens = [sp.expand(P[i, j]) for i in range(2) for j in range(2)]


def support(expr):
    expr = sp.expand(expr)
    if expr == 0:
        return []
    poly = sp.Poly(expr, *newvars)
    return [tuple(int(e) for e in m) for m in poly.monoms()]


gen_sup = [support(g) for g in gens]
jac_sup = support(Jdet)


def wdeg(sup, w):
    return min(sum(e * wi for e, wi in zip(m, w)) for m in sup)


if __name__ == "__main__":
    print("=== (2,2,2) composed achiever chart ===")
    print("Jacobian det =", Jdet, " (expect alpha^3)")
    print("generators in new coords:")
    for g in gens:
        print("   ", g)
    ma = minAdm((2, 2, 2))
    print(f"minAdm={ma}, target 2*rho = {ma} (rho=3/2)\n")

    wmax = 4
    best = None; argw = None
    hits = []
    for w in itertools.product(range(wmax + 1), repeat=len(newvars)):
        if sum(w) == 0:
            continue
        denom = min(wdeg(s, w) for s in gen_sup)
        if denom <= 0:
            continue
        num = sum(w) + wdeg(jac_sup, w)
        r = F(num, denom)
        if best is None or r < best:
            best, argw = r, w
        if r < ma:
            hits.append((r, w))
    print(f"exhaustive weight search in {{0..{wmax}}}^{len(newvars)}:")
    print(f"  min 2*rho = {best} (rho={best/2}); minAdm={ma}")
    print(f"  argmin w (aligned to {[str(v) for v in newvars]}) = {argw}")
    print(f"  UNDERSHOOTS (2*rho < minAdm): {len(hits)}")
    for (r, w) in hits[:10]:
        print(f"    2rho={r} at w={w}  <== KILL CANDIDATE")
    print("\nVERDICT:", "SURVIVE (no undershoot in this chart)" if not hits else "KILL FOUND")
