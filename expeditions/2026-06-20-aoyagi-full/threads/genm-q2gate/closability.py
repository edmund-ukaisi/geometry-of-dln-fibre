from functools import lru_cache
from fractions import Fraction as F
def redChain(t,M): return (t,)+M[2:]
@lru_cache(maxsize=None)
def minAdm(M):
    n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm(redChain(t,M)) for t in range(0,min(M[0],M[1])+1))
# Closability criterion for the a=0 shell brick (u=min(M0,M1)=M0<=M1, saturated waist):
#   reaches threshold  <=>  min_k codim_k/gamma_k >= R/(R-1),  R = minAdm(redChain u M)/minAdm(M).
# Give the R/(R-1) TARGET per cell (satred supplies true gamma_k; closable iff min_k codim_k/gamma_k >= target).
print("cell | minAdm(M) | u=min | redChain u M | minAdm(rc) | R=minAdm(rc)/minAdm(M) | TARGET R/(R-1) | square?")
tests=[(3,3,3,3),(3,4,4,4),(3,5,5,5),(3,4,5,5),(4,4,4,4),(3,3,4,4),(4,5,5,5),(3,6,6,6),(3,4,4,4,4)]
for M in tests:
    if min(M[0],M[1])<3: continue
    u=min(M[0],M[1]); rc=redChain(u,M)
    mM=minAdm(M); mrc=minAdm(rc)
    R=F(mrc,mM)
    tgt = R/(R-1) if R>1 else F(10**9)
    sq = (M[0]==M[1])
    print(f"{M} | {mM} | {u} | {rc} | {mrc} | {R} | {tgt} | {'SQUARE' if sq else 'wide b='+str(M[1]-u)}")
print()
print("Reference (square, PROVEN inheriting): (3,3,3,3) binding corank-2 codim4/gamma1=4; TARGET=7 ⟹ 4<7 ⟹ INHERITS. ✓")
print("For wide cells: coupled-closable-for-sure iff min_k codim_k/gamma_k(TRUE) >= TARGET (satred supplies true gamma_k).")
