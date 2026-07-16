# FINAL verification of the complete 2-case concavity proof (the formalizable strategy).
# Facts used: F1 D(x)<=E(x); F2 smin nondecreasing; IH E concave.
# Case A smin(x)<=x-1: anchor s=smin(x), affine-in-x => D(x-1)+D(x+1)<=2 D(x).
# Case B smin(x)=x:  Δ(x)=D(x+1)-E(x) <= E(x+1)-E(x) [F1] <= E(x)-E(x-1) [IH] <= E(x)-D(x-1) [F1] = Δ(x-1).
from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def Dfun(tail,x): return minAdm((x,)+tuple(tail))
def Efun(tail,x): return minAdm((x,)+tuple(tail[1:]))
def gval(tail,x,s):
    M2=tail[0]; return (x-s)*(M2-s)+minAdm((s,)+tuple(tail[1:]))
def smin(tail,x):
    M2=tail[0]; best=None;arg=None
    for s in range(min(x,M2)+1):
        v=gval(tail,x,s)
        if best is None or v<best: best=v;arg=s
    return arg

F1_fail=0; F2_fail=0; caseA_fail=0; caseB_link_fail=0; total_covered=0; total=0
for taillen in range(2,5):
    for tail in product(range(1,7),repeat=taillen):
        M2=tail[0]; prev=-1
        for x in range(0,13):
            # F1
            if Dfun(tail,x)>Efun(tail,x): F1_fail+=1
            sm=smin(tail,x)
            if sm<prev: F2_fail+=1
            prev=sm
        for x in range(1,12):
            sm=smin(tail,x)
            total+=1
            if sm<=x-1:
                total_covered+=1
                if not (Dfun(tail,x-1)+Dfun(tail,x+1) <= 2*Dfun(tail,x)): caseA_fail+=1
            else:  # sm==x
                total_covered+=1
                Dx1=Dfun(tail,x+1); Ex1=Efun(tail,x+1); Ex=Efun(tail,x); Exm=Efun(tail,x-1); Dxm=Dfun(tail,x-1)
                # verify each link of the chain
                ok = (Dx1<=Ex1) and (Ex1-Ex <= Ex-Exm) and (Dxm<=Exm) and (Dfun(tail,x)==Ex)
                # and the conclusion
                concl = (Dx1 - Dfun(tail,x)) <= (Dfun(tail,x)-Dxm)
                if not (ok and concl): caseB_link_fail+=1
print(f"F1 (D<=E) failures: {F1_fail}")
print(f"F2 (smin nondecreasing) failures: {F2_fail}")
print(f"Case A (anchor-midpoint) failures: {caseA_fail}")
print(f"Case B (seam sandwich links + conclusion) failures: {caseB_link_fail}")
print(f"coverage: {total_covered}/{total} x's (every x in exactly one case)")
