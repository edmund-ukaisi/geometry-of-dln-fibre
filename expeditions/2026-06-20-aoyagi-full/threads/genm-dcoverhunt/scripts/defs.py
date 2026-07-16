"""Exact-arithmetic reimplementation of the load-bearing Lean defs, for the
hole-(d) / hsector coverage hunt.  Truncated Nat subtraction; bindingCut = LEAST achiever.

Mirrors:
  minAdm / minAdmRec   (RouteMLayerSplit)
  bindingCut           (RouteMSJAdm: Nat.find exists_binding_cut, i.e. LEAST achiever)
  tailMinWidth         (RouteMSJDeeperFlagCore: min(M1,...,Mlast))
  redChain u M = (u, M2, ..., Mlast)
  deep factor Zdeep = prod(M2,...,Mlast); generic rank = min(M2,...,Mlast)
"""
from functools import lru_cache

def sub(x, y):
    return max(0, x - y)

@lru_cache(maxsize=None)
def minAdm(M):
    # M is a tuple of positive ints, length >= 2.
    if len(M) == 2:
        return M[0] * M[1]
    best = None
    for t in range(0, min(M[0], M[1]) + 1):
        v = (M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:])
        if best is None or v < best:
            best = v
    return best

def bindingCut(M):
    # LEAST t achieving minAdm(M).
    target = minAdm(M)
    for t in range(0, min(M[0], M[1]) + 1):
        v = (M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:])
        if v == target:
            return t
    raise RuntimeError("no achiever")

def tailMinWidth(M):
    # min(M1, ..., Mlast)  (indices 1..last)
    return min(M[1:])

def redChain(u, M):
    # (u, M2, ..., Mlast)
    return (u,) + M[2:]

def deepRank(M):
    # generic rank of Zdeep = prod(M2, M3, ..., Mlast) = min over widths M[2..last]
    return min(M[2:])

def a_star(M):
    t = bindingCut(M)
    return M[0] - t

def b_star(M):
    t = bindingCut(M)
    return M[1] - t

def genuine_shell(M, j):
    # at cut u = t*+j: a = sub(M0,u) >=1, b = sub(M1,u) >=1
    t = bindingCut(M)
    u = t + j
    a = sub(M[0], u)
    b = sub(M[1], u)
    return a >= 1 and b >= 1

def nonempty_shell(M, j):
    # sub(min(M1,Mlast), j) <= M2
    t = bindingCut(M)
    q = min(M[1], M[-1])
    return sub(q, j) <= M[2]

def is_good(M):
    """GOOD chain: t*>=1 and hpiv at every genuine+nonempty shell j in [0, min(a*,b*)]."""
    t = bindingCut(M)
    if t < 1:
        return False
    a = a_star(M); b = b_star(M)
    r = min(a, b)
    w = tailMinWidth(M)
    for j in range(0, r + 1):
        if not genuine_shell(M, j):
            continue
        if not nonempty_shell(M, j):
            continue
        u = t + j
        if minAdm(redChain(u, M)) > u * w:
            return False
    return True

def carrier_codim(M):
    return minAdm(M)  # carrierThreshold = minAdm/2

if __name__ == "__main__":
    # sanity: (3,3,3), (2,2,2), (2,2,1)
    for M in [(2,2,1),(2,2,2),(3,3,3),(5,5,5),(3,3,4),(3,3,4,4),(4,3,5,5)]:
        print(M, "minAdm=",minAdm(M),"t*=",bindingCut(M),
              "a*=",a_star(M),"b*=",b_star(M),
              "M2=",M[2],"a*+b*=",a_star(M)+b_star(M),
              "deepRank=",deepRank(M),"good=",is_good(M))
