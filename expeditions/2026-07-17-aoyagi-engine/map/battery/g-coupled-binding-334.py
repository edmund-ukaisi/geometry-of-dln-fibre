#!/usr/bin/env python3
# guards: resolution-tree
# config: M=(3,3,4); minAdm=8 reached only with a corank-2 first cut
# provenance: threads/00-genesis/paper-read-cert.md §6 (coupled-binding witness)
"""Divisor-sharing necessity guard: a corank-<=1-only peel provably undershoots.

minAdm((3,3,4)) = 8, achieved at t=1 (first-cut corank 3-1 = 2). Restricting every
cut to corank <= 1 (t >= min-1 at each level) yields a strictly larger minimum, so
any tree bookkeeping that only carries rank-drop-by-one data cannot reach the true
threshold — the coupled (sharing) data is load-bearing. Exit 0 iff both values
compute exactly as stated and coupled < restricted."""
import sys
from _minadm import minAdm
from functools import lru_cache

@lru_cache(maxsize=None)
def minAdm_corank_le1(M):
    M = tuple(M)
    if len(M) == 1: return 0
    if len(M) == 2: return M[0] * M[1]
    lo = max(0, min(M[0], M[1]) - 1)
    return min((M[0] - t) * (M[1] - t) + minAdm_corank_le1((t,) + M[2:])
               for t in range(lo, min(M[0], M[1]) + 1))

full, restricted = minAdm((3, 3, 4)), minAdm_corank_le1((3, 3, 4))
ok = (full == 8) and (restricted > full)
print(f"minAdm(3,3,4)={full} (expect 8); corank<=1-restricted={restricted}; coupled strictly better: {ok}")
sys.exit(0 if ok else 1)
