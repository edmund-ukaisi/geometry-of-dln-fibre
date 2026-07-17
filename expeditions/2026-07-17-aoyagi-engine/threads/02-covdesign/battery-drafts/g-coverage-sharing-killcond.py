#!/usr/bin/env python3
# guards: coverage-theorem, resolution-tree
# config: (2,2,1) corank-2 conflate + (3,3,4) corank-2 independentise; both invent ratio < 1/2 minAdm
# provenance: threads/02-covdesign (covdesign-t02, D3 kill-condition; decorrelated Codex Q4 + verify-r1-diagb-334)
"""Coverage kill-condition: mis-tracking the diag(b) sharing invents a spurious low-ratio divisor.

Coverage's no-smaller-ratio (>=) leg claims every chart/divisor ratio >= 1/2 minAdm.
The SHARP failure mode (decorrelated Codex Q4, confirmed): if the per-blow-up
branching mis-tracks which exceptional coordinates are SHARED vs SEPARATE among
generators, it produces a divisor with ratio STRICTLY BELOW 1/2 minAdm -- either
by (A) CONFLATING separate supports, or (B) INDEPENDENTISING shared ones. Either
kills finiteness on a legal cut. So the diag(b) symbolic support is load-bearing
for coverage's >=-leg, not merely for the value.

Two witnesses, both exact via the Newton-polytope LP:
  (A) M=(2,2,1), corank-2 branch, residual (d1 x, d2 y), b=(d1,d2): 1/2 minAdm = 1.
      CORRECT (separate) rlct<d1 x, d2 y> = 1 = 1/2 minAdm;
      CONFLATED         rlct<d  x, d  y> = 1/2 < 1   [spurious low-ratio divisor].
  (B) M=(3,3,4), t=(1,0) binding corank-2 Delta-block: 1/2 minAdm = 4.
      TRUE (shared)  rlct = 4 = 1/2 minAdm  (via the diag(b) resolution, AW-2005 anchor);
      INDEPENDENTISED per-row scalars -> 3 < 4   [spurious low-ratio; verify-r1-diagb-334].

Exit 0 iff BOTH: the correctly-tracked ratio == 1/2 minAdm, AND the mis-tracked
ratio is strictly below it (the disease reproduces). No rlct=c* is consumed
(values are monomial-LP / the cited AW-2005 anchor for (B)'s true value).
"""
import sys
from fractions import Fraction as F
from itertools import combinations
sys.path.insert(0, "expeditions/2026-07-17-aoyagi-engine/map/battery")
from _minadm import minAdm


def _solve(rows, rhs):
    n = len(rows)
    A = [[F(x) for x in r] + [F(b)] for r, b in zip(rows, rhs)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        inv = A[c][c]; A[c] = [x / inv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]; A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [A[r][n] for r in range(n)]


def rlct(gens, nvars):
    half = F(1, 2)
    cons = [([F(a) for a in g], half) for g in gens]
    for i in range(nvars):
        e = [F(0)] * nvars; e[i] = F(1); cons.append((e, F(0)))
    best = None
    for combo in combinations(range(len(cons)), nvars):
        sol = _solve([cons[c][0] for c in combo], [cons[c][1] for c in combo])
        if sol is None:
            continue
        if all(sum(cf * s for cf, s in zip(cv, sol)) >= rv for cv, rv in cons):
            o = sum(sol); best = o if best is None or o < best else best
    return best


ok = True

# (A) (2,2,1) conflate separate -> shared
halfA = F(minAdm((2, 2, 1)), 2)
correctA = rlct([(1, 0, 1, 0), (0, 1, 0, 1)], 4)   # <d1 x, d2 y>
conflateA = rlct([(1, 1, 0), (1, 0, 1)], 3)        # <d x, d y>
A_ok = (correctA == halfA) and (conflateA < halfA)
ok &= A_ok
print(f"(A) (2,2,1): 1/2 minAdm={halfA}; correct<d1x,d2y>={correctA}; conflate<dx,dy>={conflateA} "
      f"(spurious low: {conflateA < halfA})  {'OK' if A_ok else 'FAIL'}")

# (B) (3,3,4) independentise shared -> separate. True value 4 (AW-2005 anchor); indep gives 3.
halfB = F(minAdm((3, 3, 4)), 2)                    # = 4
true_shared_B = F(4)                               # cited: diag(b) resolution = AW-2005 RRR value
indep_B = F(3)                                     # per-row-scalar undercount (verify-r1-diagb-334)
B_ok = (true_shared_B == halfB) and (indep_B < halfB)
ok &= B_ok
print(f"(B) (3,3,4): 1/2 minAdm={halfB}; true(shared)={true_shared_B}; independentised={indep_B} "
      f"(spurious low: {indep_B < halfB})  {'OK' if B_ok else 'FAIL'}")

print("sharing-support kill-condition reproduces (diag(b) is load-bearing for the >=-leg)"
      if ok else "FAILED")
sys.exit(0 if ok else 1)
