# Verify the sandwich proof of concavity of D_M(x)=minAdm((x,M2,...,Mlast)) for taillen>=2.
#   g(x,s)=(x-s)(M2-s)+E(s),  E(s)=minAdm((s,)+T'), domain s<=min(x,M2).  s*(x)=smallest argmin.
# Sandwich:  Delta(x):=D(x+1)-D(x).
#   (SC1) Delta(x) <= M2 - s*(x)           [s*(x) feasible at x+1]
#   (SC2) Delta(x) >= M2 - s*(x+1)  when s*(x+1)<=x  [s*(x+1) feasible at x]
#   Concavity Delta(x)<=Delta(x-1) via  Delta(x)<=M2-s*(x)<=Delta(x-1)   [SC1@x + SC2@x-1 needs s*(x)<=x-1]
#   BOUNDARY: s*(x)=x (< M2). Then need the sub-lemma  E(x)-E(x-1) >= M2-x.
from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def Dfun(tail,x): return minAdm((x,)+tuple(tail))
def sstar(tail,x):
    M2=tail[0]; Tp=tail[1:]
    best=None; arg=None
    for s in range(min(x,M2)+1):
        v=(x-s)*(M2-s)+minAdm((s,)+tuple(Tp))
        if best is None or v<best: best=v; arg=s
    return arg,best
def E(tail,s): return minAdm((s,)+tuple(tail[1:]))    # E(s)=minAdm((s,M3,...))

sc1_fail=0; sc2_fail=0; sand_fail=0; boundary_cases=0; boundary_sublemma_fail=[]
XMAX=10
for taillen in range(2,5):
    for tail in product(range(1,7),repeat=taillen):
        M2=tail[0]
        Dv=[Dfun(tail,x) for x in range(0,XMAX+2)]
        ss=[sstar(tail,x)[0] for x in range(0,XMAX+2)]
        for x in range(0,XMAX):
            Dx1=Dv[x+1]-Dv[x]
            # SC1
            if not (Dx1 <= M2 - ss[x]): sc1_fail+=1
            # SC2 when s*(x+1)<=x
            if ss[x+1] <= x:
                if not (Dx1 >= M2 - ss[x+1]): sc2_fail+=1
        # concavity via sandwich, with boundary tracking
        for x in range(1,XMAX):
            # want Delta(x) <= Delta(x-1)
            # main path uses SC2@x-1 requiring s*(x)<=x-1
            if ss[x] <= x-1:
                pass  # covered by sandwich
            else:
                # boundary: s*(x)=x (must be, since s*(x)<=min(x,M2)); check sub-lemma if x<M2
                boundary_cases+=1
                if x < M2:
                    if not (E(tail,x)-E(tail,x-1) >= M2 - x):
                        boundary_sublemma_fail.append((tail,x,E(tail,x),E(tail,x-1),M2))
            # direct concavity check anyway
            if not (Dv[x+1]-Dv[x] <= Dv[x]-Dv[x-1]): sand_fail+=1
print(f"SC1 failures: {sc1_fail}")
print(f"SC2 (when s*(x+1)<=x) failures: {sc2_fail}")
print(f"direct concavity (Delta non-incr) failures: {sand_fail}")
print(f"boundary cases s*(x)=x with x<=min: {boundary_cases}")
print(f"  boundary sub-lemma  E(x)-E(x-1) >= M2-x  FAILURES: {len(boundary_sublemma_fail)}  {boundary_sublemma_fail[:6]}")
# Also: is s*(x)=x (x<M2) even possible?  (if never, boundary is vacuous for x<M2)
bx=0
for taillen in range(2,5):
    for tail in product(range(1,7),repeat=taillen):
        M2=tail[0]
        for x in range(1,M2):   # x<M2
            if sstar(tail,x)[0]==x: bx+=1
print(f"cases with s*(x)=x AND x<M2 (genuine interior-boundary): {bx}")
