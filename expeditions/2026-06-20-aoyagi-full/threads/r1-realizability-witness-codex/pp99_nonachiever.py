#!/usr/bin/env python3
"""
#99 cap-class — the NON-ACHIEVER cell test + the (C>=) lower-bound integrity test.

The value/headline needs: (C>=) every emitted codim = Mval(M0, T_c) for SOME ADMISSIBLE T_c (=> codim
>= minAdm), and (C-exists) one codim = minAdm. The DANGER from the pinch: if a cell's T_c is read off a
NON-ADMISSIBLE / non-monotone rank-drop profile via the WRONG endpoint-only cap, could it:
  (a) yield a T_c that is NOT admissible (so Mval(M0,T_c) is not a genuine stratum codim), or
  (b) yield a codim < minAdm (breaking the lower bound le_antisymm — FATAL to the value)?

We model a "cell read" as: take ANY per-block-feasible exponent vector U (a tuple's truncation profile,
NOT necessarily monotone), form its prefix running ranks two ways (correct all-widths vs pinched
endpoint), read T_c off each, and test admissibility + Mval vs minAdm.

ALSO: the crucial structural point — the running ranks of ANY tuple are ALWAYS WEAKLY DECREASING
(rank can only drop along a product: rank(AB) <= min(rank A, rank B)). So the genuine running-rank
profile t_j is ALWAYS monotone, regardless of admissibility of the truncations. The PINCHED formula may
violate this. Test whether the genuine (exact) read is always monotone and always yields an admissible
T_c with Mval >= minAdm, and whether the pinched read can break it.
"""
import sympy as sp
from itertools import product

def tPrev(M, T, j): return M[0] if j == 0 else T[j-1]
def Mval(M, T):
    L = len(M)-1
    return sum((tPrev(M, T, j) - T[j]) * (M[j+1] - T[j]) for j in range(L))
def admBound(M, j): return min(M[0], M[1]) if j == 0 else M[j+1]
def admPred(M, T):
    L = len(M)-1
    if any(T[j] > admBound(M, j) for j in range(L)): return False
    if any(T[j] > T[i] for i in range(L) for j in range(i, L)): return False
    if L >= 1 and T[L-1] != 0: return False
    return True
def Adm(M):
    L = len(M)-1
    return [list(T) for T in product(*[range(admBound(M, j)+1) for j in range(L)]) if admPred(M, list(T))]
def minAdm(M): return min(Mval(M, T) for T in Adm(M))

def partialId(r, c, t): return sp.Matrix(r, c, lambda a, b: 1 if (a == b and a < t) else 0)
def prefix_exact(M, U):
    """exact prefix running ranks of the cascade with truncations U (arbitrary, per-block feasible)."""
    L = len(M)-1; out = [M[0]]; P = sp.eye(M[0])
    for s in range(L):
        P = partialId(M[s+1], M[s], U[s]) * P
        out.append(P.rank())
    return out
def prefix_pinch(M, U):
    """pinched endpoint-only cap running ranks (BUGGY)."""
    L = len(M)-1; out = [M[0]]
    for j in range(1, L+1):
        wmin = min(U[p] for p in range(0, j))
        out.append(min(wmin, min(M[0], M[j])))
    return out
def Tc(t): return list(t[1:])

print("=== STRUCTURAL FACT: genuine running ranks t_j are ALWAYS weakly decreasing (rank drops along products) ===")
bad_mono = 0; checked = 0
for L in [2, 3, 4]:
    for M in product(range(1, 5), repeat=L+1):
        M = list(M)
        for U in product(*[range(max(M)+1) for _ in range(L)]):
            U = list(U)
            t = prefix_exact(M, U); checked += 1
            if any(t[s] < t[s+1] for s in range(L)): bad_mono += 1
print(f"   checked {checked} (any U): genuine-prefix-NON-monotone count = {bad_mono}")
print()

print("=== (a)+(b): does a NON-achiever / arbitrary cell read break (C>=)? genuine vs pinched ===")
# For arbitrary U, read T_c off genuine and pinched prefix; test admissibility + Mval vs minAdm.
gen_nonadm = 0; gen_undershoot = 0; pinch_nonadm = 0; pinch_undershoot = 0; checked = 0
divergent = []
for L in [2, 3, 4]:
    for M in product(range(1, 5), repeat=L+1):
        M = list(M)
        mn = minAdm(M)
        if mn == 0: continue   # leaf, no non-leaf cell
        for U in product(*[range(max(M)+1) for _ in range(L)]):
            U = list(U)
            checked += 1
            tg = prefix_exact(M, U); tp = prefix_pinch(M, U)
            Tcg = Tc(tg); Tcp = Tc(tp)
            # genuine read
            if not admPred(M, Tcg): gen_nonadm += 1
            elif Mval(M, Tcg) < mn: gen_undershoot += 1
            # pinched read
            if not admPred(M, Tcp): pinch_nonadm += 1
            elif Mval(M, Tcp) < mn: pinch_undershoot += 1
            if Tcg != Tcp and len(divergent) < 10:
                divergent.append((tuple(M), tuple(U), tg, tp, Tcg, Tcp,
                                  Mval(M, Tcg), Mval(M, Tcp), admPred(M, Tcg), admPred(M, Tcp), mn))
print(f"   checked {checked} (M non-leaf, arbitrary cell profile U):")
print(f"   GENUINE read  T_c: non-admissible={gen_nonadm}, Mval<minAdm undershoot (when adm)={gen_undershoot}")
print(f"   PINCHED read  T_c: non-admissible={pinch_nonadm}, Mval<minAdm undershoot (when adm)={pinch_undershoot}")
print()
print("   sample divergent (M,U, t_gen, t_pinch, Tc_gen, Tc_pinch, Mval_gen, Mval_pinch, adm_gen, adm_pinch, minAdm):")
for d in divergent:
    print("    ", d)
