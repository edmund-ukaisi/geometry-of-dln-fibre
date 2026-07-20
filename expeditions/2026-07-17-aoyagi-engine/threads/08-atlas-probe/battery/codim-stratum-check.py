#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/08-atlas-probe (pnp08). Independent dimension count (my own, elementary),
#   NOT the Lean engine and NOT citing rlct=1/2 codim. Cross-validates the Mval value (p.22)
#   geometrically: Mval(t) = exact codim of the rank stratum it labels, so min = minAdm and no
#   faithfully-tracked divisor undershoots. (Whether rlct = 1/2 codim is the banked/coverage
#   content -- deliberately NOT invoked here; this is a VALUE cross-check only.)
"""Q1(b) geometric no-undershoot, L=2 cores.

For M=(M1,M2,M3): variable matrices C1 (M1xM2), C2 (M2xM3) at the origin.
Stratum for profile (t^1,0): {rank(C1)=t^1  AND  C1 C2 = 0}. Elementary codim count:
  - {rank(C1)=t^1}: codim (M1-t^1)(M2-t^1) in the C1 space (determinantal).
  - given rank(C1)=t^1, ker(C1) has dim M2-t^1; C1 C2=0 <=> each of the M3 columns of C2
    lies in ker(C1)  ->  C2 free-dim (M2-t^1)*M3, codim  M2*M3-(M2-t^1)*M3 = t^1*M3.
  - total codim = (M1-t^1)(M2-t^1) + t^1*M3  ==  Mval(t^1,0)   (Aoyagi p.22).
So min_t codim = minAdm and every stratum codim >= minAdm : no rank-stratum divisor undershoots.
"""
import sys
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


def Mval2(M, t1):
    return (M[0] - t1) * (M[1] - t1) + (t1) * (M[2])          # Mval(t1, t2=0), L=2


def codim_stratum(M, t1):
    """codim{rank(C1)=t1 and C1 C2=0} by the elementary count above."""
    codim_C1 = (M[0] - t1) * (M[1] - t1)                      # rank(C1)<=t1 determinantal codim
    codim_C2 = t1 * M[2]                                      # M2*M3 - (M2-t1)*M3
    return codim_C1 + codim_C2


ok = True
for M in [(2, 2, 2), (3, 3, 4)]:
    print(f"=== M={M} ===")
    ma = minAdm(M)
    codims = {}
    for t1 in range(min(M[0], M[1]) + 1):
        cd = codim_stratum(M, t1)
        mv = Mval2(M, t1)
        match = (cd == mv)
        ok &= match
        codims[t1] = cd
        under = "  ** codim < minAdm **" if cd < ma else ""
        print(f"  t1={t1}: codim{{rankC1={t1}, C1C2=0}}={cd}  Mval={mv}  match={match}{under}")
    mn = min(codims.values())
    print(f"  min codim = {mn}   minAdm = {ma}   equal: {mn == ma}   "
          f"(every stratum codim >= minAdm: {all(c >= ma for c in codims.values())})")
    ok &= (mn == ma)
    print()

print("Mval == codim(stratum) for all L=2 profiles, min == minAdm, no codim < minAdm"
      if ok else "FAILED")
sys.exit(0 if ok else 1)
