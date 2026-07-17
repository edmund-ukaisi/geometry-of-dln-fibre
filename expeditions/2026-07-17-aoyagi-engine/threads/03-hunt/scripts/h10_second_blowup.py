#!/usr/bin/env python3
"""HUNT h10 -- second blow-up of the non-NC binomial leaf (Q1(b)/Q4 self-check).

The (2,2,2) composed-chart leaf ideal has binomial generators
    al*(b*g0 + de*c210),  al*(b*g1 + de*c211)
so the chart is NOT yet normal-crossing. A divisor could in principle hide after a
FURTHER blow-up of the binomial locus {b=de=0}. We COMPOSE that blow-up (both standard
charts) onto the leaf, recompute the exact Jacobian (gains a factor rho), and re-run the
exact vertex-enum min ratio. If the min stays >= minAdm, no sub-threshold divisor hides
below this leaf (corroborating the 'no new smaller ratio from blowing up' folklore here).
"""
import sys
import sympy as sp
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/threads/03-hunt/scripts")
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm
from h7_chart_lp import min_ratio_exact

al, a, g0, g1, c210, c211 = sp.symbols("al a g0 g1 c210 c211")
rho, e, f = sp.symbols("rho e f")


def leaf_after_blowup(which):
    """which='b': b=rho, de=rho*e ; 'de': de=rho, b=rho*f. Returns (newvars, gen_sup, jac_sup)."""
    if which == "b":
        b_e, de_e = rho, rho * e
        extra = e
        # Jacobian of (b,de)->(rho,e): det[[1,0],[e,rho]] = rho
        subJac = rho
    else:
        b_e, de_e = rho * f, rho
        extra = f
        subJac = rho
    # leaf generators (from h5, corrected labels): al g0, al g1, al(b g0+de c210), al(b g1+de c211)
    gens = [al * g0, al * g1,
            al * (b_e * g0 + de_e * c210),
            al * (b_e * g1 + de_e * c211)]
    newvars = [al, a, rho, extra, g0, g1, c210, c211]
    # total Jacobian: original chart al^3 (from incidence) times this sub-blowup's rho.
    # (the shear had Jac 1; 'a' is inert here.) We fold al^3 * rho into the jac support.
    Jtot = sp.expand(al**3 * subJac)

    def sup(expr):
        expr = sp.expand(expr)
        return [] if expr == 0 else [tuple(int(x) for x in m) for m in sp.Poly(expr, *newvars).monoms()]
    gen_sup = [sup(g) for g in gens]
    jac_sup = sup(Jtot)
    return newvars, gen_sup, jac_sup, gens, Jtot


if __name__ == "__main__":
    ma = minAdm((2, 2, 2))
    for which in ("b", "de"):
        nv, gs, js, gens, Jt = leaf_after_blowup(which)
        best, argw = min_ratio_exact(gs, js, len(nv))
        print(f"=== (2,2,2) leaf + blow-up of binomial locus, chart '{which}' ===")
        print(f"   gens: {gens}")
        print(f"   total Jacobian: {Jt}")
        print(f"   EXACT min 2rho = {best} (rho={best/2}); minAdm={ma}  "
              f"-> {'SURVIVE' if best >= ma else 'KILL'}")
