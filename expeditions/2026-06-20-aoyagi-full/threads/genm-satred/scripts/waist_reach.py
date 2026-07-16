"""
Reliable exact-N: does the SATURATED a=0 (and b=0 mirror) waist reach 1/2minAdm(M) via the
FRONT-factor rank-sector? Confirm m_I = minAdm(M) exactly (the recursion), and the A vs 2Delta split.

a=0 saturated: u=M0<=M1 => a=M0-u=0, b=M1-u, u+b=M1. z~0 = X.Y (X=[P|B12] M0xM1 full-row-rank M0,
Y=[z0;A_cor] M1xM2). Front-factor rank-sector: stratify rank(z~0)=r, strata s=M0-r in 0..M0 reduce to
chain (s,M2,...)=redChain s M with charge (M0-s)(M1-s); m_I = min_s[(M0-s)(M1-s)+minAdm(redChain s M)].
Claim: m_I = minAdm(M) EXACTLY (s ranges over the SAME cuts as the minAdm recursion).

Also the A vs 2Delta split (satred): A=max_j j(M2-b-j), 2Delta=minAdm(redChain u M)-minAdm(M).
A<=2Delta => clean pointwise fold; A>2Delta => needs the joint (front) rank-sector.
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
def densityA(u,b,M2):
    return max([0]+[j*(M2-b-j) for j in range(1,min(u,M2)+1)])

WMAX=7
cells=0; mI_fail=0; clean=0; needs_sector=0; ex=[]
for arity in (4,5):
    for M in product(range(1,WMAX+1),repeat=arity):
        M0,M1,M2=M[0],M[1],M[2]
        # saturated a=0: u=M0, need u<=M1 (M0<=M1) and u<=min(M0,M1)=M0 => a=0,b=M1-M0>=0
        if M0>M1: continue     # a=0 branch (M0<=M1); b=0 mirror is M0<->M1 symmetric
        u=M0; a=0; b=M1-u
        rc=redChain(u,M); mM=minAdm(M)
        # front-factor rank-sector m_I = min_{0<=s<=u}[(M0-s)(M1-s)+minAdm(redChain s M)]  (u=M0)
        mI = min((M0-s)*(M1-s)+minAdm(redChain(s,M)) for s in range(0,u+1))
        cells+=1
        if mI != mM: mI_fail+=1
        A=densityA(u,b,M2); twoD=minAdm(rc)-mM
        if A<=twoD: clean+=1
        else:
            needs_sector+=1
            if len(ex)<6: ex.append((M,u,b,M2,A,twoD))
print(f"a=0 saturated cells (M0<=M1, arity 4,5, widths<= {WMAX}): {cells}")
print(f"  m_I != minAdm(M) (front-rank-sector min): {mI_fail}  (expect 0 => m_I=minAdm(M), the recursion)")
print(f"  A<=2Delta CLEAN pointwise fold: {clean}")
print(f"  A>2Delta NEEDS the joint front rank-sector: {needs_sector}")
for e in ex: print("    needs-sector (M,u,b,M2,A,2D):",e)
