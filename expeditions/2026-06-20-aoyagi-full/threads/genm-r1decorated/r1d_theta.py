from functools import lru_cache
import itertools
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def is_adm(M,T):
    L=len(T)
    for j in range(L):
        if T[j]>admBound(M,j): return False
    for i in range(L):
        for j in range(L):
            if i<=j and T[j]>T[i]: return False
    if L>=1 and T[L-1]!=0: return False
    return True
def adm_cone(M):
    L=len(M)-1
    return [T for T in itertools.product(*[range(admBound(M,j)+1) for j in range(L)]) if is_adm(M,T)]
def Mval(M,T):
    s=0
    for j in range(len(T)):
        tprev=M[0] if j==0 else T[j-1]; s+=(tprev-T[j])*(M[j+1]-T[j])
    return s
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-x)*(M[1]-x)+minAdm((x,)+M[2:]) for x in range(min(M[0],M[1])+1))

# Verify: for a partial profile pi=(t1,...,tk), min over completions T>=pi of Mval = A(pi)+minAdm(remChain).
# remChain(pi) = (t_k, M_{k+1}, ..., M_L); A(pi)= sum_{j<=k}(t_{j-1}-t_j)(M_j - t_j), t0=M0.
def Apart(M,pi):
    s=0
    for j in range(len(pi)):
        tprev=M[0] if j==0 else pi[j-1]; s+=(tprev-pi[j])*(M[j+1]-pi[j])
    return s
def remChain(M,pi):
    k=len(pi); return (pi[-1],)+tuple(M[k+1:]) if k>=1 else M
def min_completions(M,pi):
    L=len(M)-1; best=None
    for T in adm_cone(M):
        if T[:len(pi)]==tuple(pi):
            v=Mval(M,T); best=v if best is None else min(best,v)
    return best

bad=0; tot=0
for M in itertools.product(range(1,5),repeat=4):
    cone=adm_cone(M)
    # all admissible prefixes (proper + full)
    prefixes=set()
    for T in cone:
        for k in range(1,len(T)+1): prefixes.add(T[:k])
    for pi in prefixes:
        mc=min_completions(M,list(pi))
        if mc is None: continue
        rhs=Apart(M,list(pi))+minAdm(remChain(M,list(pi)))
        tot+=1
        if mc!=rhs: bad+=1
print(f"Theta identity  min_{{T>=pi}}Mval == A(pi)+minAdm(remChain pi):  {tot-bad}/{tot} match, {bad} FAIL")
print("=> Theta(M,pi)=1/2(min Mval - A(pi)) = 1/2 minAdm(remChain pi).  (collapses to repo minAdm o remChain)" if bad==0 else "IDENTITY FAILS -- fix cert (A)")
