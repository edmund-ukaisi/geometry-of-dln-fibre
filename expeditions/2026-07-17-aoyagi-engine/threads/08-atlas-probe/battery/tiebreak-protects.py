#!/usr/bin/env python3
# guards: resolution-tree
# provenance: threads/08-atlas-probe (pnp08), o4 item-1. Reuses the validated simulator via importlib.
"""What does the Def-4 tie-break MINIMALITY protect? (reconciles cert-atlas-probe-2222 (c) with the o4 reshape)

Compare the CORRECT chooser (componentwise-MIN of the eligible set) vs a WRONG chooser
(componentwise-MAX) on NON-bottleneck instances (where full total-comparability is maintainable):

  - Chain_viol     : incomparable pair among ALL carried divisors (full total-comparability, paper p.15)
  - SameLevel_viol : incomparable pair among divisors at a COMMON t~ level (the reshaped operative invariant)

FINDING (below): the WRONG pick breaks FULL total-comparability but PRESERVES SameLevelChainInv.
So the tie-break minimality protects FULL comparability (maintainable only at non-bottleneck instances),
NOT the operative SameLevelChainInv (which ANY eligible pick preserves). cert-2222 (c)'s "protects
total-comparability" is correct, scoped to non-bottleneck; the operative invariant does not consume
minimality.
"""
import sys
import importlib.util
import io
import contextlib

_spec = importlib.util.spec_from_file_location("_sim", "nonmono-2232-sim.py")
_m = importlib.util.module_from_spec(_spec)
try:
    with contextlib.redirect_stdout(io.StringIO()):
        _spec.loader.exec_module(_m)
except SystemExit:
    pass
Sim = _m.Sim


def comparable(a, b):
    return all(p <= q for p, q in zip(a, b)) or all(p >= q for p, q in zip(a, b))


class Chk(Sim):
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


class ChkWrong(Chk):
    def def4_min(self, cands):        # WRONG: pick the componentwise-MAX eligible divisor
        for c in cands:
            if all(all(a >= b for a, b in zip(c[0], d[0])) for d in cands):
                return c
        return cands[-1]


ok = True
print("instance     chooser        Chain_viol   SameLevel_viol")
for M in [(2, 2, 2, 2), (2, 2, 3, 2), (3, 3, 4)]:      # non-bottleneck
    sc = Chk(M, headreset="runmin", check_inv=True).run()
    sw = ChkWrong(M, headreset="runmin", check_inv=True).run()
    print(f"  M={str(M):12s} min (correct)   {sc.chainv:3d}          {sc.samev:3d}")
    print(f"  M={str(M):12s} MAX (wrong)     {sw.chainv:3d}          {sw.samev:3d}")
    # correct preserves both; wrong preserves SameLevel; wrong breaks full-chain where there's room.
    ok &= (sc.chainv == 0 and sc.samev == 0 and sw.samev == 0)
    if M == (2, 2, 2, 2):
        ok &= (sw.chainv > 0)      # the wrong pick DOES break full-chain here

print("\nVERDICT: minimality protects FULL comparability (non-bottleneck); SameLevelChainInv is"
      "\npreserved by ANY eligible pick (minimality-free)." if ok else "\nUNEXPECTED")
sys.exit(0 if ok else 1)
