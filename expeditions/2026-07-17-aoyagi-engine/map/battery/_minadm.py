"""Shared exact minAdm recursion, verbatim from lean RouteMLayerSplit.minAdmRec:
Fin 1 -> 0 ; Fin 2 -> M0*M1 ; >=3 widths ->
  min_{0<=t<=min(M0,M1)} (M0-t)(M1-t) + minAdm((t,) + M[2:]).
Integers only."""
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
