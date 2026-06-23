import sympy as sp, numpy as np
from itertools import product
# THE BRIDGE SEED: do Adm M (Lambda, 1-index rank vector + Mval) and RealizableRank M (Core, rankFn =
# 2-index partial-product ranks, Set.range) AGREE on the achievable rank patterns? Specifically: is the
# achiever T* (Lambda) always realizable by an actual tuple (Core rankFn)?
#
# Adm M: T=(t_1..t_L), t_j = rank(C_1···C_j) on {∏=0} (so t_L=0), weakly-decreasing, 0≤t_j≤min(t_{j-1},M^{j+1}).
# RealizableRank: the rankFn patterns rankFn(A) = {rank of every partial product A_i···A_{j-1}} for some
#   tuple A. For a CHAIN (the DLN case), the relevant ranks are the consecutive partial products t_j.
#
# CLAIM (Gabriel / the seed): for a type-A chain, a rank vector T is REALIZABLE (= some tuple achieves it)
# IFF it satisfies the realizability inequalities — which are EXACTLY Adm's (weakly-decreasing + the
# t_j ≤ min(t_{j-1}, M^{j+1}) feasibility). So Adm = the realizable rank vectors. Verify by CONSTRUCTION:
# for each admissible T, build an explicit tuple achieving it (the rank-descent normal form).

def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))
def admissible(M,t):
    L=len(M)-1; tt=[M[0]]+list(t)
    if tt[-1]!=0: return False
    for j in range(1,L+1):
        if not(0<=tt[j]<=tt[j-1]): return False
        if tt[j]>M[j]: return False
    return True

def realize_tuple(M, t):
    # Build an explicit chain C_s : (r+M_s) x (r+M_{s+1})? No — here M IS the width (B=0 core, full widths).
    # M = (M_0,...,M_L) widths; C_s : M_s x M_{s+1}. Want rank(C_1···C_j) = t_j. Construct via the
    # rank-descent: C_s = a projection-like matrix realizing the prescribed partial-product rank.
    # Simplest: C_s = diag-ish with t_j ones cascading. Use the canonical realization: C_s maps the first
    # t_s coords to the first t_s, then the bottleneck min enforces the drop.
    L=len(M)-1; tt=[M[0]]+list(t)
    Cs=[]
    for s in range(L):
        msin=M[s]; msout=M[s+1]
        C=np.zeros((msin,msout))
        # to get rank(C_1..C_j)=t_j: make C_s the rank-(t_{s+1}) projection compatible with t_s.
        # canonical: C_s has 1's on the diagonal for the first t_{s+1} positions (the surviving rank), if
        # t_{s+1} ≤ min(t_s, msout). This makes the running product rank = t_{s+1} (the prescribed).
        rk = tt[s+1]
        for i in range(min(rk, msin, msout)): C[i,i]=1.0
        Cs.append(C)
    # compute actual partial-product ranks
    P=np.eye(M[0]); ranks=[]
    for s in range(L):
        P=P@Cs[s]; ranks.append(int(round(np.linalg.matrix_rank(P))))
    return tuple(ranks)

print("Adm M vs RealizableRank (by explicit construction) — does every admissible T get realized?")
for M in [(2,2,2),(3,2,3),(3,3,3),(2,2,2,2),(4,3,2)]:
    L=len(M)-1
    adm=[t for t in product(*[range(M[0]+1)]*L) if admissible(M,t)]
    minM=min(Mval(M,t) for t in adm); achievers=[t for t in adm if Mval(M,t)==minM]
    realized=[]
    for t in adm:
        got = realize_tuple(M,t)
        if got==tuple(t): realized.append(t)
    all_real = (set(realized)==set(adm))
    Tstar=achievers[0]
    Tstar_real = (realize_tuple(M,Tstar)==tuple(Tstar))
    print(f"  M={M}: |Adm|={len(adm)}, realized {len(realized)}/{len(adm)} by construction; ALL admissible realizable: {all_real}")
    print(f"    achiever T*={Tstar} (Mval={minM}): realizable by explicit tuple: {Tstar_real}")
