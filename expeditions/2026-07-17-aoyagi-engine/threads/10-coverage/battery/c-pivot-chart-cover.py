#!/usr/bin/env python3
"""Battery for the per-blow-up LOCAL COVERING LEMMA at corank >= 2 (T3 rung 1).

The atom coverage folds from: the blow-up of R^d at the coordinate origin is covered by
its d standard affine "pivot" charts, in the MAX-MODULUS normalization.

  pivotChart i (u) : Fin d -> R,   (pivotChart i u) k = u_i           if k = i
                                                        = u_i * u_k       if k != i
  pivotChartDom i R = { u : |u_i| <= R  and  |u_k| <= 1 for k != i }

Claims checked (exact rational arithmetic; no float tolerance in the decisive checks):
  (COVER)   cubeBox d R  subset of  U_i  pivotChart i '' pivotChartDom i R     [the load-bearing dir]
  (BOUND)   pivotChart i '' pivotChartDom i R  subset of  cubeBox d R          [gives the equality]
  (GAP)     a single FIXED pivot (corner-only) does NOT cover -- reproduces the probe's
            explicit gap witness (0, eps): index-0 corner chart misses it, index-1 pivot hits it.
  (JAC)     |det D(pivotChart i)| = |u_i|^(d-1)  -- confirms the exceptional-divisor exponent,
            so the chart folds into LeafJacobian (|det Dbeta| = prod |u|^(divExp-1)).

Everything is elementary; the cover reduces to "every finite nonempty tuple has an argmax of |.|".
"""
from fractions import Fraction as F
import itertools, sys

def pivot_chart(i, u):
    d = len(u)
    return [u[i] if k == i else u[i] * u[k] for k in range(d)]

def in_dom(i, u, R):
    d = len(u)
    return abs(u[i]) <= R and all(abs(u[k]) <= 1 for k in range(d) if k != i)

def cover_point(x, R):
    """Return a pivot i and preimage u with pivot_chart(i,u)=x and u in dom, or None.
    Uses the max-modulus coordinate as the pivot (the uniform recipe)."""
    d = len(x)
    # argmax of |x_k|
    i = max(range(d), key=lambda k: abs(x[k]))
    if x[i] == 0:
        # x is the origin (all coords <= 0 in modulus): any u with u_i=0 works
        u = [F(0)] * d
        u[i] = F(0)
        for k in range(d):
            if k != i:
                u[k] = F(0)
    else:
        u = [F(0)] * d
        u[i] = x[i]
        for k in range(d):
            if k != i:
                u[k] = x[k] / x[i]
    if pivot_chart(i, u) == x and in_dom(i, u, R):
        return i, u
    return None

fails = 0

# ---- (COVER) exhaustive rational grid over cubeBox d R, several d incl. corank>=2 ----
for d in (1, 2, 3, 4):
    R = F(1)
    grid = [F(a, 2) for a in range(-2, 3)]  # {-1,-1/2,0,1/2,1} -- inside [-R,R]
    n_checked = 0
    for x in itertools.product(grid, repeat=d):
        x = list(x)
        res = cover_point(x, R)
        n_checked += 1
        if res is None:
            print(f"[COVER FAIL] d={d} x={x} not covered by any pivot chart")
            fails += 1
    print(f"(COVER) d={d}: {n_checked} grid points, all covered by some pivot chart")

# ---- (BOUND) images stay in the box: random rational u in dom -> chart(u) in cubeBox ----
import random
random.seed(0)
for d in (2, 3, 4):
    R = F(3)
    for _ in range(2000):
        i = random.randrange(d)
        u = [F(random.randint(-3, 3), random.randint(1, 3)) for _ in range(d)]
        # force into dom
        # pivot within [-R,R], ratios within [-1,1]
        if abs(u[i]) > R:
            u[i] = R * (1 if u[i] > 0 else -1)
        for k in range(d):
            if k != i and abs(u[k]) > 1:
                u[k] = F(1) * (1 if u[k] > 0 else -1)
        x = pivot_chart(i, u)
        if not all(abs(x[k]) <= R for k in range(d)):
            print(f"[BOUND FAIL] d={d} i={i} u={u} -> x={x} escapes cubeBox R={R}")
            fails += 1
print("(BOUND) images of pivotChartDom stay in cubeBox d R (2000 samples x d in {2,3,4})")

# ---- (GAP) corner-only cover misses points; the probe's (0, eps) witness ----
# residual block C^(1) = [[0, eps],[0,0]] flattened -> only entry (0,1)=eps nonzero.
# In d=2 residual coords (c11, c12): x = (0, eps).
eps = F(1, 7)
x = [F(0), eps]
# corner chart i=0 (pivot = c11): requires u_0 = x_0 = 0 as pivot, then x_1 = u_0*u_1 = 0 != eps
corner_ok = False
# try to hit x with pivot 0 under ANY u
# pivot_chart(0,u) = (u0, u0*u1); to equal (0,eps): u0=0 => second coord 0 != eps. impossible.
if any(pivot_chart(0, [F(0), r]) == x for r in (F(-1), F(0), F(1), F(1,2))):
    corner_ok = True
# pivot chart i=1 (pivot = c12) hits it:
res1 = cover_point(x, F(1))
if corner_ok:
    print("[GAP FAIL] corner chart i=0 unexpectedly covers (0,eps)")
    fails += 1
elif res1 is None or res1[0] != 1:
    print(f"[GAP FAIL] full family failed to cover (0,eps) via a non-corner pivot: {res1}")
    fails += 1
else:
    print(f"(GAP) corner-only (pivot 0) MISSES (0,eps); full family covers it via pivot {res1[0]}, "
          f"u={res1[1]}  -- reproduces cert-atlas-probe Verdict 1(b) gap")

# ---- (JAC) |det D(pivotChart i)| = |u_i|^(d-1)  (symbolic) ----
try:
    import sympy as sp
    for d in (2, 3, 4):
        for i in range(d):
            us = sp.symbols(f'u0:{d}', real=True)
            xk = [us[i] if k == i else us[i]*us[k] for k in range(d)]
            Jac = sp.Matrix([[sp.diff(xk[k], us[m]) for m in range(d)] for k in range(d)])
            det = sp.simplify(Jac.det())
            expect = us[i]**(d-1)
            if sp.simplify(det - expect) != 0:
                print(f"[JAC FAIL] d={d} i={i}: det={det} != u_i^{d-1}")
                fails += 1
    print("(JAC) |det D(pivotChart i)| = |u_i|^(d-1) for d in {2,3,4}, all pivots "
          "-- exceptional-divisor exponent folds into LeafJacobian")
except ImportError:
    print("(JAC) sympy unavailable -- skipped (non-decisive)")

print()
if fails == 0:
    print("ALL CHECKS PASSED -- the max-modulus pivot-chart family covers cubeBox d R (= equality);")
    print("corner-only has the probe's explicit gap; Jacobian exponent is |u_i|^(d-1).")
    sys.exit(0)
else:
    print(f"{fails} CHECK(S) FAILED")
    sys.exit(1)
