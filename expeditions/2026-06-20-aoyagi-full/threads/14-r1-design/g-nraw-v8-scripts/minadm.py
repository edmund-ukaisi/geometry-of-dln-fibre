"""Exact minAdm(M) = min_{T in Adm} Mval(M,T), transcribing the Lean defs (Lambda.lean).

M : (L+1)-vector of widths (Fin (L+1) -> N).  T : L-vector of exponents (Fin L -> N).
tPrev j = M0 if j==0 else T[j-1].
Mval = sum_{j=0..L-1} (tPrev j - T[j]) * (M[j+1] - T[j]).
admBound j = min(M0,M1) if j==0 else M[j+1].
admPred: T[j] <= admBound j ; weakly decreasing (i<=j -> T[j]<=T[i]) ; T[L-1]=0.
minAdm = min Mval over Adm.
"""
from itertools import product
from functools import lru_cache

def adm_bound(M, j):
    L = len(M) - 1
    if j == 0:
        return min(M[0], M[1])
    return M[j+1]

def mval(M, T):
    L = len(M) - 1
    tot = 0
    for j in range(L):
        tprev = M[0] if j == 0 else T[j-1]
        tot += (tprev - T[j]) * (M[j+1] - T[j])
    return tot

def adm_list(M):
    L = len(M) - 1
    ranges = [range(adm_bound(M, j) + 1) for j in range(L)]
    out = []
    for T in product(*ranges):
        # weakly decreasing: i<=j -> T[j] <= T[i]
        if all(T[j] <= T[i] for i in range(L) for j in range(i, L)):
            # last exponent = 0 (j.val = L-1)
            if L >= 1 and T[L-1] != 0:
                continue
            out.append(T)
    return out

def min_adm(M):
    return min(mval(M, T) for T in adm_list(M))

def argmin_adm(M):
    best = None; bestT=[]
    for T in adm_list(M):
        v = mval(M, T)
        if best is None or v < best:
            best = v; bestT=[T]
        elif v == best:
            bestT.append(T)
    return best, bestT

if __name__ == "__main__":
    # sanity vs Lean #guard: lambdaCore = minAdm/2
    for M, want_lc in [((2,2,2),1.5),((2,1,2),1.0),((2,2,2,2),1.5),((3,3,3,3),3.0)]:
        ma = min_adm(M)
        print(M, "minAdm=",ma, "lambdaCore=",ma/2, "want",want_lc, "OK" if ma/2==want_lc else "MISMATCH")
