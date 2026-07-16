"""
Refine: classify b=1 a<u cuts by the tie index k = a+b-rho (rho=tailMinWidth=min(M1..Mlast)):
  k<=0 : sub-tie (a+b<=rho)   -- typically Brick-D convergent interior
  k==1 : the corank-one TIE (a+b=rho+1)
  k>=2 : DEEP corank
For each class report the pointwise-fold reach (satred density-order A<=2Delta+a).
A = max_{1<=j<=min(u,M2)} j*(M2-1-j)  (b=1). 2Delta = minAdm(redChain u M)-minAdm(M).
This tells WHICH cells the coupled pointwise fold handles cleanly vs needs joint rank-sector.
NO MC.
"""
from functools import lru_cache
from itertools import product
def redChain(u,M): return (u,)+tuple(M[2:])
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)<=1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm(redChain(t,M)) for t in range(min(M[0],M[1])+1))
def densityA(u,M2):
    return max([0]+[j*(M2-1-j) for j in range(1,min(u,M2)+1)])

WMAX=7
from collections import defaultdict
tot=defaultdict(int); under=defaultdict(int); ex=defaultdict(list)
for arity in (4,5):
    for M in product(range(1,WMAX+1),repeat=arity):
        M0,M1,M2=M[0],M[1],M[2]
        u=M1-1
        if u<1 or u>min(M0,M1): continue
        a=M0-u
        if a<1 or not (a<u): continue
        rho=min(M[1:])
        k=a+1-rho              # b=1
        cls = 'sub(k<=0)' if k<=0 else ('TIE(k=1)' if k==1 else 'DEEP(k>=2)')
        rc=redChain(u,M); twoD=minAdm(rc)-minAdm(M); A=densityA(u,M2)
        tot[cls]+=1
        if A > twoD + a:
            under[cls]+=1
            if len(ex[cls])<4: ex[cls].append((M,u,a,rho,A,twoD,twoD+a))
for cls in ['sub(k<=0)','TIE(k=1)','DEEP(k>=2)']:
    print(f"{cls:12s}: {tot[cls]:5d} cells, pointwise-fold UNDERSHOOTS {under[cls]:5d}  ({'CLEAN' if under[cls]==0 else 'NOT clean'})")
    for e in ex[cls]: print(f"     under (M,u,a,rho,A,2D,2D+a): {e}")
