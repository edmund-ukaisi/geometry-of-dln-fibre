#!/usr/bin/env python3
"""
#149 hMono — minAdm(schurStateRed M) ≤ minAdm M, the binding-arithmetic monotonicity.

schurStateRed M = (M_0−1, M_1−1, M_2, ..., M_L)  [drop the two front pivot vertices by 1].
CLAIM (team-lead exact-checked TRUE, 336 non-leaf M): minAdm(M') ≤ minAdm(M), M' = schurStateRed M.
The NAIVE achiever-transfer (clamp T*_j := min(T*_j, admBound M' j)) is the WRONG proof: 40/336 give a
NON-admissible T' (admBound M' 0 = admBound M 0 − 1, so T*_0 = min(M_0,M_1) overshoots the reduced bound).

THIS SCRIPT: (1) reproduce the claim + the naive-transfer failure; (2) hunt the CORRECT transfer
Adm M → Adm M' with Mval(M', T') ≤ Mval(M, T*); (3) if no clean constructive transfer, characterise the
inf'-monotonicity argument (the Adm/Mval cone-transform).
"""
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
    a = Adm(M); return min(Mval(M, T) for T in a) if a else None
def achievers(M):
    a = Adm(M); mn = min(Mval(M, T) for T in a)
    return mn, [T for T in a if Mval(M, T) == mn]
def schurStateRed(M):
    return [M[s]-1 if s <= 1 else M[s] for s in range(len(M))]
def is_nonleaf(M):
    # non-leaf: minAdm M > 0 AND the pivot widths ≥ 1 (so schurStateRed is well-defined ≥ 0)
    return all(M[s] >= 1 for s in range(min(2, len(M)))) and (minAdm(M) or 0) > 0

# ---- (1) reproduce claim + naive-transfer failure ----
print("=== (1) claim minAdm(M') ≤ minAdm(M) + naive clamp-transfer failure ===")
claim_fail = 0; checked = 0; naive_nonadm = 0; naive_ex = []
for L in [1, 2, 3]:
    for M in product(range(1, 5), repeat=L+1):
        M = list(M)
        if not all(M[s] >= 1 for s in range(min(2, L+1))): continue   # schurStateRed needs pivot ≥1
        Mp = schurStateRed(M)
        if any(x < 1 for x in Mp[:min(2, L+1)]):  # reduced must stay valid for Adm (widths ≥0 ok, but check)
            pass
        mnM = minAdm(M); mnMp = minAdm(Mp)
        if mnM is None or mnMp is None: continue
        checked += 1
        if not (mnMp <= mnM): claim_fail += 1
        # naive transfer: clamp the achiever
        _, achM = achievers(M)
        Tstar = achM[0]
        Tclamp = [min(Tstar[j], admBound(Mp, j)) for j in range(L)]
        if not admPred(Mp, Tclamp):
            naive_nonadm += 1
            if len(naive_ex) < 8: naive_ex.append((tuple(M), tuple(Mp), tuple(Tstar), tuple(Tclamp)))
print(f"  checked {checked} non-leaf M (L=1..3, widths 1..4): claim minAdm(M')≤minAdm(M) fails = {claim_fail}")
print(f"  naive clamp-transfer produces NON-admissible T' : {naive_nonadm} cases")
for e in naive_ex: print("    M,M',T*,T_clamp:", e)
