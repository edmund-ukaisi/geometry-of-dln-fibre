import itertools
from functools import lru_cache
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def Mval(M,T):
    L=len(T); s=0
    for j in range(L):
        tprev=M[0] if j==0 else T[j-1]
        s+=(tprev-T[j])*(M[j+1]-T[j])
    return s
def admissible(M,T):
    L=len(T)
    for j in range(L):
        if T[j]>admBound(M,j): return False
        if j>0 and T[j]>T[j-1]: return False
    return T[L-1]==0
def adm_cone(M):
    L=len(M)-1; return [T for T in itertools.product(*[range(admBound(M,j)+1) for j in range(L)]) if admissible(M,T)]
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-x)*(M[1]-x)+minAdm((x,)+M[2:]) for x in range(min(M[0],M[1])+1))
# want a 4-width chain (L=3) whose BINDING branch has a layer j with a ≥2×2 corank block AND downstream
# product (>=1 layer after j). corank block at layer j (1-indexed): rows (t_{j-1}-... ) -- use the
# "drop" dims. Simplest proxy: layer-1 drop with (M0-t1)>=2 and (M1-t1)>=2 => 2x2+ corank block at
# boundary 0, with >=2 downstream layers (C2,C3 product).
print("smallest coupled corank-2 4-chains (binding branch has layer-1 corank block ≥2×2, downstream product):")
found=[]
for M in itertools.product(range(1,5),repeat=4):
    L=3; cone=adm_cone(M); 
    if not cone: continue
    mm=minAdm(M); binding=[T for T in cone if Mval(M,T)==mm]
    for T in binding:
        t1=T[0]; c_rows=M[0]-t1; c_cols=M[1]-t1
        if c_rows>=2 and c_cols>=2:      # layer-1 corank block ≥ 2×2
            found.append((sum(M),M,T,mm,(c_rows,c_cols)))
            break
found.sort()
for tot,M,T,mm,blk in found[:8]:
    print(f"  M={M} (Σ={tot}): binding T={T}, minAdm={mm} ½={mm/2}, layer-1 corank block={blk[0]}×{blk[1]}, downstream=C2·C3 product({M[1]}×{M[2]}·{M[2]}×{M[3]})")
