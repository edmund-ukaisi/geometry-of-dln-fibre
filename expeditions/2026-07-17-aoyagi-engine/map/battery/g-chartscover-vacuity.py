#!/usr/bin/env python3
# guards: region-glue, coverage-theorem
# config: (2,2,2) fake atlas chartDom=univ, divExp={4}; c'=8/5 in [3/2,2) satisfies hyps, conclusion FALSE
# provenance: threads/04-bridge (t04-bridge; r2 finding 2 — the ChartsCover vacuity bug made executable)
"""r2 finding 2 made executable: the CURRENT region_glue signature is INSUFFICIENT (a counterexample).

region_glue currently reads:
    (hcov : ChartsCover M t) -> (hrat : forall e in terminalExponents, c' < e/2)
        -> routeMLayerBoxIntegral M c' 1 < top.
`ChartsCover` only constrains the leaf `chartDom` as an abstract Set: nothing ties `chartDom` to the
actual chart map / the monomialisation of the loss. So `chartDom = Set.univ` satisfies `ChartsCover`
VACUOUSLY (U = univ covers; univ is open), for ANY divExp data. Then the conclusion can be FALSE:

  M = (2,2,2): true rlct = 1/2 minAdm = 3/2, so for c' > 3/2 the box integral DIVERGES (= top)
               -- the banked achiever / <=-leg (exact: minAdm(2,2,2)=3).
  Fake atlas: one leaf, chartDom = univ (satisfies ChartsCover), divExp = {4}.
  Pick c' = 8/5 in [3/2, 2):
     hrat holds:  c' = 8/5 < 4/2 = 2  (below every terminal ratio).      TRUE
     hcov holds:  chartDom = univ.                                        TRUE
     conclusion:  routeMLayerBoxIntegral(2,2,2, 8/5) = top  (c' > 3/2).   FALSE

So (hcov and hrat) hold while the conclusion fails: the current signature does NOT imply finiteness.
The FIX (this thread's design): region_glue must consume the per-leaf CoV BRIDGE (chart map +
loss-pullback + Jacobian ledger + IMAGE cover), which ties chartDom to the monomial data and forces
the divExp to be the TRUE resolution exponents. With the bridge, divExp={4} for (2,2,2) is impossible
(the true binding divisor has exponent 3, ratio 3/2), so no such counterexample exists.

Exit 0 iff the counterexample is confirmed: hyps satisfiable AND c' in (1/2 minAdm, min divExp/2).
"""
import sys
from fractions import Fraction as F
from functools import lru_cache


@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(int(x) for x in M)
    if len(M) == 1:
        return 0
    if len(M) == 2:
        return M[0] * M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(min(M[0], M[1])+1))


M = (2, 2, 2)
half_minAdm = F(minAdm(M), 2)          # 3/2 -- true 1/2 minAdm; box diverges for c' > this
fake_divExp = [4]                      # a fake atlas's terminal exponents (chartDom = univ)
min_ratio = min(F(e, 2) for e in fake_divExp)   # 2 -- the fake hrat bound
cprime = F(8, 5)                       # in [3/2, 2)

# current signature's hypotheses (chartDom=univ => ChartsCover holds; hrat below):
hcov_holds = True                      # ChartsCover satisfied by all-univ chartDom (open + covers)
hrat_holds = (cprime < min_ratio)      # c' < every terminal ratio
# the TRUE conclusion for this c' (exact): box integral finite iff c' < 1/2 minAdm
conclusion_true = (cprime < half_minAdm)
counterexample = hcov_holds and hrat_holds and (not conclusion_true)

print(f"M={M}: 1/2 minAdm = {half_minAdm} (box diverges for c' > this, banked achiever/<=-leg)")
print(f"fake atlas: chartDom=univ, divExp={fake_divExp}, min ratio = {min_ratio}")
print(f"c' = {cprime}:  ChartsCover holds={hcov_holds}, hrat (c'<ratio) holds={hrat_holds}, "
      f"true finiteness (c'<1/2 minAdm)={conclusion_true}")
print(f"=> CURRENT region_glue signature has a COUNTEREXAMPLE (hyps hold, conclusion false): {counterexample}")
print("=> the chart<->integrand CoV bridge is REQUIRED (ties chartDom to the true monomial exponents)."
      if counterexample else "no counterexample (unexpected)")
sys.exit(0 if counterexample else 1)
