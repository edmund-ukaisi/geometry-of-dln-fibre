#!/usr/bin/env python3
"""
genM_structure.py — EXACT-algebra reconstruction of the binding descent path for general M.

Goal: for a reduced-width vector M = (M_0,...,M_L), recover
  - minAdm M (via the Aoyagi layer-peeling recursion, the exact integer min),
  - the binding minimiser T* = (t_1,...,t_L) (the descent path),
  - the per-step Schur-complement codim contributions  c_j = (M'_0 - t_{j+1})(M'_1 - t_{j+1})
    along the peel (M' = current reduced chain),
  - the "single-pivot box-divergence threshold" prediction: ½·minAdm.

This is the COMBINATORIAL layer (no measure theory yet) — it identifies the achiever path the
geometric chart must blow up.  Everything is exact integer arithmetic.
"""
from functools import lru_cache
from itertools import product


def Mval(M, T):
    """Aoyagi candidate value (over the integers).  M : tuple len L+1, T : tuple len L.
    M(T) = sum_{j=1}^{L} (t^{j-1} - t^j)(M^{j+1} - t^j),  with t^0 := M^1 = M[0]."""
    L = len(M) - 1
    assert len(T) == L
    total = 0
    for j in range(L):           # j = 0..L-1 corresponds to layer index 1..L
        tprev = M[0] if j == 0 else T[j - 1]
        tj = T[j]
        total += (tprev - tj) * (M[j + 1] - tj)
    return total


def admBound(M, j):
    """min(M0,M1) for j==0, else M_{j+1}."""
    if j == 0:
        return min(M[0], M[1])
    return M[j + 1]


def admissible(M, T):
    L = len(M) - 1
    # within block bounds
    for j in range(L):
        if T[j] > admBound(M, j):
            return False
    # weak decrease t^1 >= ... >= t^L
    for i in range(L):
        for j in range(i, L):
            if T[j] > T[i]:
                return False
    # last exponent zero
    if L >= 1 and T[L - 1] != 0:
        return False
    return True


def all_adm(M):
    L = len(M) - 1
    if L == 0:
        yield tuple()
        return
    ranges = [range(admBound(M, j) + 1) for j in range(L)]
    for T in product(*ranges):
        if admissible(M, T):
            yield T


def minAdm_brute(M):
    """min over Adm of Mval, with the minimiser(s)."""
    best = None
    bestT = []
    for T in all_adm(M):
        v = Mval(M, T)
        if best is None or v < best:
            best = v
            bestT = [T]
        elif v == best:
            bestT.append(T)
    return best, bestT


def redChain(t, M):
    """(t, M_2, M_3, ..., M_L) — one fewer layer."""
    return (t,) + tuple(M[2:])


@lru_cache(maxsize=None)
def minAdmRec(M):
    """Layer-peeling recursion, returns (value, descent-path-as-list-of-pivots)."""
    L = len(M) - 1
    if L == 0:
        return 0, ()
    if L == 1:
        return M[0] * M[1], ()        # leaf: pivot product, no further pivots
    best = None
    bestpath = None
    bestt = None
    for t in range(min(M[0], M[1]) + 1):
        childval, childpath = minAdmRec(redChain(t, M))
        v = (M[0] - t) * (M[1] - t) + childval
        if best is None or v < best:
            best = v
            bestpath = childpath
            bestt = t
    return best, (bestt,) + bestpath


def descent_trace(M):
    """Full peel: list of (current chain, pivot t, schur-codim, child-leaf-or-recurse)."""
    trace = []
    cur = tuple(M)
    val, path = minAdmRec(tuple(M))
    # path has length L-1 (pivots at each >=3-width step); the final L=1 leaf product is implicit.
    idx = 0
    while len(cur) >= 3:
        t = path[idx]
        codim = (cur[0] - t) * (cur[1] - t)
        trace.append((cur, t, codim, 'recurse'))
        cur = redChain(t, cur)
        idx += 1
    # now cur is a 2-width leaf
    leaf = cur[0] * cur[1]
    trace.append((cur, None, leaf, 'leaf'))
    return trace, val


def report(M):
    M = tuple(M)
    bval, bTs = minAdm_brute(M)
    rval, rpath = minAdmRec(M)
    trace, tval = descent_trace(M)
    print(f"M = {M}")
    print(f"  minAdm (brute over Adm)      = {bval}   minimiser(s) T* = {bTs}")
    print(f"  minAdmRec (layer-peel)       = {rval}   peel pivots     = {rpath}")
    print(f"  descent-trace total          = {tval}")
    assert bval == rval == tval, "recursion / brute / trace disagree!"
    print(f"  rlct = minAdm/2              = {bval/2}")
    print("  peel:")
    for (chain, t, codim, kind) in trace:
        if kind == 'leaf':
            print(f"     LEAF chain={chain}  product-codim = {codim}")
        else:
            print(f"     chain={chain}  pivot t={t}  schur-codim=(M0-t)(M1-t)={codim}")
    # the achiever-monomial: the SUM of schur-codims + the leaf = minAdm; the box-divergence
    # threshold the single weighted-pivot chart must realise is minAdm/2.
    print()
    return bval, bTs, rpath, trace


if __name__ == "__main__":
    for M in [(2, 2, 2), (3, 3, 4), (3, 3, 3), (4, 4, 2, 2), (2, 2, 4),
              (4, 4, 4), (5, 3, 4), (3, 3, 3, 3), (2, 3, 4, 2), (4, 4, 4, 4)]:
        report(M)
