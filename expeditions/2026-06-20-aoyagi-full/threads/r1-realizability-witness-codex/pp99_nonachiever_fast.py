#!/usr/bin/env python3
"""
#99 cap-class — NON-ACHIEVER cell test, FAST.
Two parts:
  PART 1 (pure combinatorial, exhaustive): for arbitrary cell profile U (per-block window-min source),
    form T_c via the CORRECT all-widths cap vs the PINCHED endpoint-only cap, and test whether the
    PINCHED read can produce a codim Mval(M0,T_c) that is < minAdm (FATAL: breaks the le_antisymm lower
    bound) or a NON-admissible T_c (breaks (C>=)). The genuine read is the all-widths formula.
  PART 2 (sympy exact, SMALL sweep): confirm the genuine running-rank read = the all-widths formula on a
    small adversarial interior-pinch set, so PART 1's "correct read" is the true matrix read.
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
def minAdm(M):
    a = Adm(M); return min(Mval(M, T) for T in a) if a else 0

def Tc_allwidths(M, U):
    """genuine all-widths running-rank read: t_j = min(window-min U over [0,j), min over widths M_0..M_j); T_c=t[1:]."""
    L = len(M)-1
    return [min(min(U[p] for p in range(0, j)), min(M[r] for r in range(0, j+1))) for j in range(1, L+1)]
def Tc_pinch(M, U):
    """buggy endpoint-only cap: t_j = min(window-min U, min(M_0,M_j)); T_c=t[1:]."""
    L = len(M)-1
    return [min(min(U[p] for p in range(0, j)), min(M[0], M[j])) for j in range(1, L+1)]

print("=== PART 1 (combinatorial, exhaustive): can the PINCHED read break (C>=)? ===")
checked = 0
gen_nonadm = gen_undershoot = 0
pinch_nonadm = pinch_undershoot = 0
pinch_divergent_codim = []
for L in [2, 3, 4]:
    for M in product(range(1, 5), repeat=L+1):
        M = list(M)
        mn = minAdm(M)
        if mn == 0: continue                          # leaf
        for U in product(range(0, 5), repeat=L):       # arbitrary cell profile, truncations 0..4
            U = list(U)
            checked += 1
            Tg = Tc_allwidths(M, U); Tp = Tc_pinch(M, U)
            if not admPred(M, Tg): gen_nonadm += 1
            elif Mval(M, Tg) < mn: gen_undershoot += 1
            if not admPred(M, Tp): pinch_nonadm += 1
            elif Mval(M, Tp) < mn: pinch_undershoot += 1
            if Tg != Tp:
                cg = Mval(M, Tg) if admPred(M, Tg) else None
                cp = Mval(M, Tp) if admPred(M, Tp) else None
                if (cg != cp) and len(pinch_divergent_codim) < 12:
                    pinch_divergent_codim.append((tuple(M), tuple(U), Tg, Tp, cg, cp, admPred(M, Tg), admPred(M, Tp), mn))
print(f"  checked {checked} (M non-leaf, arbitrary U):")
print(f"  GENUINE all-widths read:  non-admissible T_c = {gen_nonadm};  Mval<minAdm undershoot = {gen_undershoot}")
print(f"  PINCHED endpoint read:    non-admissible T_c = {pinch_nonadm};  Mval<minAdm undershoot = {pinch_undershoot}")
print(f"  cases where pinched vs genuine T_c give DIFFERENT (admissible) codim: {len(pinch_divergent_codim)}")
for d in pinch_divergent_codim[:12]:
    print("    M,U,Tc_gen,Tc_pinch,codim_gen,codim_pinch,adm_gen,adm_pinch,minAdm:", d)
print()

print("=== PART 2 (sympy exact, small): genuine running-rank read == all-widths formula on interior-pinch M ===")
def partialId(r, c, t): return sp.Matrix(r, c, lambda a, b: 1 if (a == b and a < t) else 0)
def prefix_exact(M, U):
    L = len(M)-1; out = [M[0]]; P = sp.eye(M[0])
    for s in range(L):
        P = partialId(M[s+1], M[s], U[s]) * P
        out.append(P.rank())
    return out
bad = 0; checked2 = 0
# interior-pinch M's (a middle width strictly below both neighbours), small widths, all U
pinchMs = [[3,1,3], [3,1,3,3], [4,2,1,3], [2,1,2], [3,2,1,2], [4,1,4,1,4]]
for M in pinchMs:
    L = len(M)-1
    for U in product(range(0, max(M)+1), repeat=L):
        U = list(U)
        t_exact = prefix_exact(M, U)
        t_formula = [M[0]] + Tc_allwidths(M, U)
        checked2 += 1
        if t_exact != t_formula:
            bad += 1
            if bad <= 5: print("    MISMATCH", M, U, t_exact, t_formula)
print(f"  interior-pinch M's, all U: exact prefix ranks == all-widths formula: checked={checked2} mismatches={bad}")
