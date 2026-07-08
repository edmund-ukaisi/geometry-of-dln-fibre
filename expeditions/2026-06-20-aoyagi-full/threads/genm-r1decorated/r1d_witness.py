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
    ranges=[range(admBound(M,j)+1) for j in range(L)]
    return [T for T in itertools.product(*ranges) if is_adm(M,T)]
def Mval(M,T):
    L=len(T); s=0
    for j in range(L):
        tprev=M[0] if j==0 else T[j-1]
        s+=(tprev-T[j])*(M[j+1]-T[j])
    return s
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-x)*(M[1]-x)+minAdm((x,)+M[2:]) for x in range(min(M[0],M[1])+1))

# Anchors (cross-check the object)
for M,exp in [((2,2,2),3),((3,3,4),8),((4,4,2,2),4)]:
    print(f"  anchor minAdm{M}={minAdm(M)} (expect {exp}) {'OK' if minAdm(M)==exp else 'X'}")

print("\n=== Find smallest 4-node chains (L=3) whose BINDING branch has layer-1 corank>=2 AND >=2 deeper layers active ===")
# layer-1 corank at cut t1 = min(M0-t1, M1-t1); need >=2. deeper product = C3*C4 nontrivial (both active).
cands=[]
for M in itertools.product(range(1,5),repeat=4):
    if M[0]<M[1]: continue  # WLOG-ish reduce dup by symmetry (not needed but trims)
    cone=adm_cone(M); mm=minAdm(M)
    binding=[T for T in cone if Mval(M,T)==mm]
    for T in binding:
        t1=T[0]
        cor1=min(M[0]-t1, M[1]-t1)
        # deeper layers active: t1>0 (so there's a deeper chain (t1,M2,M3)) and the deeper product C3.C4
        # is a genuine product => need M3>=1 i.e. 4 nodes and the reduced chain (t1,M2,M3) has L>=2
        if cor1>=2 and t1>=1:
            cands.append((M,T,mm,cor1))
            break
for M,T,mm,cor1 in cands[:25]:
    print(f"  M={M} binding T={T} minAdm={mm} (rlct={mm/2}) layer1-corank={cor1}")
print(f"  total candidates: {len(cands)}")
