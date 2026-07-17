#!/usr/bin/env python3
"""HUNT h7 -- EXACT fractional-program min ratio over a chart (vertex enumeration).

For a chart with generator monomial supports {e_m} (exponent vectors over new coords)
and Jacobian support {f_j}, the induced-valuation ratio is scale-invariant:

    2*rho(w) = ( sum_i w_i + min_j (w . f_j) ) / ( min over gen-monomials m of w . e_m ).

Normalize the denominator to 1: minimize the CONCAVE numerator  N(w) = sum w + min_j w.f_j
over the polytope  P = { w >= 0 : w . e_m >= 1  for every generator-monomial m }.
A concave function on P attains its min at a VERTEX of P; enumerate vertices exactly
(n tight constraints among the (#gen-monomials + n nonneg)), evaluate N exactly, take
the min. This is the TRUE continuous min ratio for the chart (no grid truncation) --
so 'no undershoot' here is a real per-chart certificate, not a sampled one.
"""
from fractions import Fraction as F
from itertools import combinations


def _solve(rows, rhs):
    n = len(rows)
    A = [[F(x) for x in r] + [F(b)] for r, b in zip(rows, rhs)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        inv = A[c][c]
        A[c] = [x / inv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [A[r][n] for r in range(n)]


def min_ratio_exact(gen_sup, jac_sup, nvars):
    """gen_sup: list (per generator) of list of exponent tuples. jac_sup: list of exponent
    tuples (the Jacobian det's monomials). Returns exact min 2*rho (Fraction) and argmin w."""
    # gen-monomial constraints: w . e >= 1
    gmons = []
    for g in gen_sup:
        for m in g:
            gmons.append([F(x) for x in m])
    cons = [(cm, F(1)) for cm in gmons]
    for i in range(nvars):
        e = [F(0)] * nvars
        e[i] = F(1)
        cons.append((e, F(0)))          # w_i >= 0
    jf = [[F(x) for x in f] for f in jac_sup] if jac_sup else None
    best = None; argw = None
    idxs = list(range(len(cons)))
    for combo in combinations(idxs, nvars):
        rows = [cons[c][0] for c in combo]
        rhs = [cons[c][1] for c in combo]
        sol = _solve(rows, rhs)
        if sol is None:
            continue
        if any(s < 0 for s in sol):
            continue
        # feasibility: every gen-monomial constraint satisfied
        ok = True
        for (cv, rv) in cons:
            if sum(cf * s for cf, s in zip(cv, sol)) < rv - F(1, 10**9):
                ok = False
                break
        if not ok:
            continue
        # denom = min gen-monomial value; must be >0 (it's >=1 by feasibility)
        num = sum(sol)
        if jf:
            num += min(sum(cf * s for cf, s in zip(f, sol)) for f in jf)
        # ratio = num / denom, denom normalized to the min gen-monomial value
        denom = min(sum(cf * s for cf, s in zip(gm, sol)) for gm in gmons)
        if denom <= 0:
            continue
        rr = F(num, 1) / denom
        if best is None or rr < best:
            best, argw = rr, tuple(sol)
    return best, argw


if __name__ == "__main__":
    import sys
    sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
    from _minadm import minAdm
    # cross-check on the (2,2,2) composed chart
    sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/threads/03-hunt/scripts")
    import h5_composed_chart_222 as h5
    best, argw = min_ratio_exact(h5.gen_sup, h5.jac_sup, len(h5.newvars))
    print(f"(2,2,2) exact chart min 2*rho = {best} (rho={best/2}); minAdm=3  "
          f"{'SURVIVE' if best >= 3 else 'KILL'}")
    import h6_composed_chart_2222 as h6
    best6, argw6 = min_ratio_exact(h6.gen_sup, h6.jac_sup, len(h6.newvars))
    print(f"(2,2,2,2) exact chart min 2*rho = {best6} (rho={best6/2}); minAdm=3  "
          f"{'SURVIVE' if best6 >= 3 else 'KILL'}")


def min_ratio_lp(gen_sup, jac_sup, nvars):
    """LP min ratio when the numerator is LINEAR (Jacobian a single monomial, as for
    incidence charts). Solves  min c.w  s.t.  w.e_m >= 1 (all gen-monomials), w >= 0,
    where c = ones + jac_exponent. Float (HiGHS); LP optimum is rational, so we also
    return the basic weight for exact re-verification. A GUIDE that is exact-at-vertex."""
    import numpy as np
    from scipy.optimize import linprog
    assert jac_sup is None or len(jac_sup) == 1, "numerator not linear (multi-monomial Jac)"
    c = np.ones(nvars)
    if jac_sup:
        for i, e in enumerate(jac_sup[0]):
            c[i] += e
    A = []
    for g in gen_sup:
        for m in g:
            A.append([-float(x) for x in m])   # -w.e <= -1
    b = [-1.0] * len(A)
    res = linprog(c=c, A_ub=A, b_ub=b, bounds=[(0, None)] * nvars, method="highs")
    return (res.fun if res.success else None), (res.x if res.success else None)
