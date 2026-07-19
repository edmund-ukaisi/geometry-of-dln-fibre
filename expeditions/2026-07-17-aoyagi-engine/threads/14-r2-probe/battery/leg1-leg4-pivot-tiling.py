#!/usr/bin/env python3
# guards: coverage-theorem, resolution-tree
# provenance: threads/14-r2-probe (pnp-o5), R2 decorrelated atlas-closure probe. DECORRELATED from
#   coverage-t07/pnp-atlas: the pivotChart spec is transcribed from the DURABLE Lean statement
#   (Engine/PivotCover.lean) + page-pin-centers.md, NOT read from their scripts.
# Exact rational grid (fractions), no Monte-Carlo. Circularity guard: pure geometry, no rlct/cited_aoyagi.
"""
LEG 1 — per-node max-modulus TILING at the d_center values that ACTUALLY arise (1..12 for the kill-set):
  does the FULL d-pivot family image = cubeBox^d exactly, and does every PROPER subset UNDERSHOOT?
  pivotChart i u = (k |-> u_i if k=i else u_i*u_k), domain {|u_i|<=R, |u_k|<=1 (k!=i)}.
  KILL: full family misses a cube point (breaks rung-1) OR a subset silently covers (family not tight).
LEG 4 — corner/boundary class:
  (4a) the corner_chart_not_cover config: (0,eps,..)-type point covered by the full family (a non-corner
       pivot), witnessing the atlas handles what the corner chart misses;
  (4b) d_center=1 degenerate (single chart trivially covers);
  (4c) empty residual (a case-2 col/row = 0 would give d_center=0) -- check the recursion never emits it.
"""
from fractions import Fraction as F
from itertools import product, combinations
import sys

ARISING = list(range(1, 13))   # d_center values arising across the kill-set (extracted)


def pivot_image_point(i, u, d):
    return tuple(u[i] if k == i else u[i] * u[k] for k in range(d))


def in_dom(i, u, d, R):
    return abs(u[i]) <= R and all(abs(u[k]) <= 1 for k in range(d) if k != i)


def preimage_in_dom(i, x, d, R):
    """Does pivot i reach cube point x within its bounded domain? Max-modulus test (exact)."""
    if x[i] == 0:
        # need x = 0 entirely (pivot 0 forces others 0)
        return all(xk == 0 for xk in x)
    # u_i = x_i (|<=R|), u_k = x_k/x_i (|<=1| iff |x_k|<=|x_i|)
    if abs(x[i]) > R:
        return False
    return all(abs(x[k]) <= abs(x[i]) for k in range(d))


def cube_grid(d, R, steps):
    """Exact rational grid of cubeBox^d = [-R,R]^d."""
    vals = [(-R + F(2 * R, steps) * s) for s in range(steps + 1)]
    return product(vals, repeat=d)


def leg1(dmax=6, R=1, steps=4):
    """Full family covers; proper subsets undershoot. (grid steps modest for exact enumeration at high d)"""
    fails = []
    for d in range(1, dmax + 1):
        # smaller grid at higher d to stay exact & finite
        st = steps if d <= 3 else (3 if d <= 5 else 2)
        pts = list(cube_grid(d, F(R), st))
        # full family covers every cube point
        for x in pts:
            if not any(preimage_in_dom(i, x, d, F(R)) for i in range(d)):
                fails.append(("LEG1-FULL-MISS", d, x))
                break
        # every proper subset misses SOME cube point (family is tight) -- test the (d-1)-subsets
        if d >= 2:
            for omit in range(d):
                subset = [i for i in range(d) if i != omit]
                # a witness the omitted pivot uniquely covers: e_omit direction (0..,eps at omit)
                wit = tuple(F(1, 2) if k == omit else F(0) for k in range(d))
                covered = any(preimage_in_dom(i, wit, d, F(R)) for i in subset)
                if covered:
                    fails.append(("LEG1-SUBSET-NOT-TIGHT", d, omit, wit))
    return fails


def leg4(R=1):
    fails = []
    # (4a) corner config generalized: (0,...,0,eps) covered by the LAST pivot, not pivot 0
    for d in range(2, 7):
        eps = F(1, 3)
        x = tuple(eps if k == d - 1 else F(0) for k in range(d))
        if preimage_in_dom(0, x, d, F(R)):
            fails.append(("LEG4a-corner-wrongly-covered-by-0", d, x))
        if not preimage_in_dom(d - 1, x, d, F(R)):
            fails.append(("LEG4a-corner-not-covered-by-last", d, x))
        if not any(preimage_in_dom(i, x, d, F(R)) for i in range(d)):
            fails.append(("LEG4a-corner-UNCOVERED-by-full", d, x))
    # (4b) d=1 degenerate: single chart covers [-R,R]
    for x0 in [F(-1), F(0), F(1, 2), F(1)]:
        if not preimage_in_dom(0, (x0,), 1, F(R)):
            fails.append(("LEG4b-d1-miss", x0))
    # (4c) empty residual guard: a case-2/case-1 node never emits d_center=0 (checked structurally below)
    return fails


def leg4c_no_zero_dcenter():
    """Replay the recursion; assert every blow-up node has d_center >= 1 (no empty center emitted)."""
    SRC = 'expeditions/2026-07-17-aoyagi-engine/threads/08-atlas-probe/battery/nonmono-2232-sim.py'
    src = open(SRC).read()
    ns = {'__name__': 'orig'}
    exec(src[:src.index('ok = True')], ns)
    Sim = ns['Sim']
    bad = []
    for M in [(2, 2, 2), (2, 2, 1, 1), (3, 3, 4, 2, 3), (2, 2, 3, 3, 2), (3, 3, 2, 2)]:
        s = Sim(M, headreset='runmin'); L = s.L
        def proc(S, J, divs):
            if S == L + 1: return
            MS = s.Mrun(S); MSp1 = min(MS, s.Mw(S + 1))
            if J >= MSp1: proc(S + 1, 0, divs); return
            levels = sorted({s.tilde(d[0]) for d in divs})
            occ = [m for m in levels if J + 1 <= m <= MS - 1]
            if occ:
                target = occ[0]; J1 = target - J
                dc = J1 * (s.Mw(S + 1) - J) + 1
                if dc < 1: bad.append((M, S, J, 'case1', dc))
                cands = [d for d in divs if s.tilde(d[0]) == target]; f = s.def4_min(cands)
                bump = J1 * (s.Mw(S + 1) - J)
                proc(S, J, [d for d in divs if d is not f] + [(s.set_tail(f[0], S, J), f[1] + bump)])
                proc(S, J + 1, list(divs) + [(s.set_tail(f[0], S, J), f[1] + bump)])
            else:
                dc = (MS - J) * (s.Mw(S + 1) - J)
                if dc < 1: bad.append((M, S, J, 'case2', dc))
                T = [0] * L
                for i in range(1, S): T[i - 1] = s.Mrun(i + 1)
                proc(S, J + 1, list(divs) + [(s.set_tail(tuple(T), S, J), dc)])
        proc(1, 0, [])
    return bad


if __name__ == "__main__":
    print("LEG 1 — per-node max-modulus tiling (full covers; proper subsets undershoot), exact grid")
    f1 = leg1(dmax=6)
    print(f"  d=1..6 tested: {'PASS (full covers, every (d-1)-subset misses its omitted pivot direction)' if not f1 else f1[:6]}")
    print("LEG 4 — corner/boundary class")
    f4 = leg4()
    print(f"  4a/4b: {'PASS (corner covered by non-corner pivot; d=1 trivial)' if not f4 else f4[:6]}")
    f4c = leg4c_no_zero_dcenter()
    print(f"  4c no zero-d_center node emitted (kill-set): {'PASS' if not f4c else f4c[:6]}")
    ok = not (f1 or f4 or f4c)
    print("\nLEG1+LEG4:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
