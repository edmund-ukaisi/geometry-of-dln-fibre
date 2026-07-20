#!/usr/bin/env python3
# guards: resolution-tree
# provenance: threads/08-atlas-probe (pnp08), o4 task. Reuses the VALIDATED profile simulator
#   (nonmono-2232-sim.py) via importlib. Integer-only, exact.
"""o4 CompChainInv scope: the paper's FULL total-comparability (p.15) is FALSE at interior
width-drops; the WEAKER SameLevelChainInv (same-t~ divisors comparable) holds everywhere and
suffices for the chooser (o2). Value (min == minAdm) safe everywhere.

Checks, at EVERY reachable state, in the corrected runmin/FIX-A construction:
  Chain_viol      : any incomparable pair among ALL carried divisors  (paper p.15 invariant)
  SameLevel_viol  : any incomparable pair among divisors at a COMMON t~ level  (the reshaped o4)
  comp_viol(elig) : any incomparable pair in a Case-1 ELIGIBLE set  (o2 min-existence)
  value           : min over t~=0 leaf divisors == minAdm  (no undershoot)

Predicted scope of the full-chain failure (proved on these instances):
  Chain_viol > 0  <=>  running-min drops below M(2) at an INTERIOR layer, i.e.
                        exists 3<=S<=L with min(M^1..M^S) < min(M^1,M^2)  (interior bottleneck).
"""
import sys
import importlib.util
import io
import contextlib
from functools import lru_cache


@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(int(x) for x in M)
    if len(M) == 1:
        return 0
    if len(M) == 2:
        return M[0] * M[1]
    return min((M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:])
               for t in range(min(M[0], M[1]) + 1))


def comparable(a, b):
    return all(p <= q for p, q in zip(a, b)) or all(p >= q for p, q in zip(a, b))


def interior_bottleneck(M):
    """exists 3<=S<=L (1-indexed layers; L=len(M)-1) with min(M^1..M^S) < min(M^1,M^2)."""
    L = len(M) - 1
    m2 = min(M[0], M[1])
    run = m2
    for S in range(3, L + 1):        # layers 3..L
        run = min(run, M[S - 1])
        if run < m2:
            return True
    return False


# load the validated simulator without running its __main__
_spec = importlib.util.spec_from_file_location("_sim", "nonmono-2232-sim.py")
_m = importlib.util.module_from_spec(_spec)
try:
    with contextlib.redirect_stdout(io.StringIO()):
        _spec.loader.exec_module(_m)
except SystemExit:
    pass
Sim = _m.Sim


class SimScope(Sim):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.chainv = 0
        self.samev = 0

    def _check(self, S, J, divs):
        Ts = [d[0] for d in divs]
        for i in range(len(Ts)):
            for j in range(i + 1, len(Ts)):
                if not comparable(Ts[i], Ts[j]):
                    self.chainv += 1
        from collections import defaultdict
        bl = defaultdict(list)
        for T in Ts:
            bl[min(T)].append(T)
        for _, g in bl.items():
            for i in range(len(g)):
                for j in range(i + 1, len(g)):
                    if not comparable(g[i], g[j]):
                        self.samev += 1


INSTANCES = [
    (2, 2, 2), (3, 3, 4), (2, 2, 2, 2), (2, 2, 3, 2), (2, 2, 3, 3, 2), (3, 2, 4, 2),
    (2, 2, 2, 1), (3, 2, 2, 2), (3, 3, 4, 2), (3, 3, 3, 1),                       # drops but NO interior bottleneck
    (2, 2, 1, 1), (3, 3, 1, 1), (3, 3, 2, 2), (4, 4, 2, 2), (4, 4, 3, 2),
    (3, 3, 2, 1), (2, 2, 1, 2), (2, 2, 2, 1, 1),                                  # interior bottleneck
]

ok = True
print("instance         interior-bottleneck  Chain_viol  SameLevel_viol  comp_viol(elig)  value(min==minAdm)")
for M in INSTANCES:
    s = SimScope(M, headreset="runmin", check_inv=True).run()
    divs = set()
    for leaf in s.leaves:
        divs.update(leaf)
    t0min = min((mm for (T, mm) in divs if min(T) == 0), default=None)
    ib = interior_bottleneck(M)
    value_ok = (t0min == minAdm(M))
    # EXPECTATIONS: SameLevel always 0; comp_viol(elig) always 0; value always ok;
    #               Chain_viol > 0  iff interior-bottleneck.
    exp_ok = (s.samev == 0 and len(s.comp_violations) == 0 and value_ok
              and ((s.chainv > 0) == ib))
    ok &= exp_ok
    print(f"  M={str(M):15s} {str(ib):5s}               {s.chainv:3d}         {s.samev:3d}"
          f"             {len(s.comp_violations):3d}            {value_ok}   {'OK' if exp_ok else 'MISMATCH'}")

print()
print("VERDICT: SameLevelChainInv + eligible-chain hold everywhere (0); value safe everywhere;")
print("full total-comparability (paper p.15) fails EXACTLY at interior bottlenecks." if ok else "PATTERN MISMATCH")
sys.exit(0 if ok else 1)
