# CHECK Codex's clean r* = achieverRankPattern: for i<j it claims rankFn(i,j) = T_{j-1} = t*_j
# (column-constant, i-INDEPENDENT). The cascade gives rankFn(i,j) = min(t*_j, M_i, M_j) (survivors,
# using monotone window-min = t*_j). Codex's clean form is correct IFF t*_j <= min(M_i,M_j) for all i<j.
# i.e. t*_j <= M_i for all i<j  AND  t*_j <= M_j.  Verify exhaustively for ADMISSIBLE T (and find ANY
# counterexample where the cascade rankFn(i,j) < T_{j-1}, which would make Codex's clean form FALSE).
from itertools import product
import numpy as np
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def admPred(M,T):
    L=len(M)-1
    if any(T[j]>admBound(M,j) for j in range(L)): return False
    for i in range(L):
        for j in range(i,L):
            if T[j]>T[i]: return False
    if L>=1 and T[L-1]!=0: return False
    return True
def Adm(M):
    L=len(M)-1
    return [list(T) for T in product(*[range(admBound(M,j)+1) for j in range(L)]) if admPred(M,list(T))]
def tstar(M,T): return [M[0]]+list(T)
def partialId(r,c,tt):
    Cm=np.zeros((r,c))
    for k in range(min(tt,r,c)): Cm[k,k]=1.0
    return Cm
def rankFn_cascade(M,T):
    L=len(M)-1; blocks=[partialId(M[s+1],M[s],T[s]) for s in range(L)]; R={}
    for i in range(L+1):
        for j in range(L+1):
            if i<j:
                P=blocks[i].copy()
                for s in range(i+1,j): P=blocks[s]@P
                R[(i,j)]=int(round(np.linalg.matrix_rank(P,tol=1e-9)))
            elif i==j: R[(i,j)]=M[i]
            else: R[(i,j)]=0
    return R
def codex_rstar(M,T):  # achieverRankPattern: i<j -> T_{j-1}; i=j -> M_i; else 0
    L=len(M)-1; t=tstar(M,T); R={}
    for i in range(L+1):
        for j in range(L+1):
            if i<j: R[(i,j)]=t[j]   # T_{j-1} = t*_j
            elif i==j: R[(i,j)]=M[i]
            else: R[(i,j)]=0
    return R

fails=[]; checked=0
for L in [2,3,4]:
    for M in product(range(1,6),repeat=L+1):
        M=list(M)
        for T in Adm(M):
            checked+=1
            Rc=rankFn_cascade(M,T); Rx=codex_rstar(M,T)
            for k in Rc:
                if Rc[k]!=Rx[k]:
                    fails.append((M,T,k,Rc[k],Rx[k]))
print(f"checked {checked} admissible (L=2..4, widths 1..5)")
print(f"Codex achieverRankPattern (i<j -> T_{{j-1}}) vs cascade rankFn: mismatches = {len(fails)}")
if fails:
    print("FIRST 8 mismatches (M,T,(i,j),cascade,codex):")
    for f in fails[:8]: print("  ",f)
else:
    print("  => Codex's clean column-constant r* (i<j -> T_{j-1}) EQUALS cascade rankFn on ALL admissible T.")
    print("     i.e. t*_j <= min(M_i,M_j) holds for all i<j, admissible -> survivors cap never bites below t*_j.")
