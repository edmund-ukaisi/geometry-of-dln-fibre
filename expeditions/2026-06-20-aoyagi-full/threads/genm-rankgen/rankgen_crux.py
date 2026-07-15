import itertools
from functools import lru_cache
@lru_cache(maxsize=None)
def minAdm(M):
    if len(M)==2: return M[0]*M[1]
    M0,M1=M[0],M[1]
    return min((M0-t)*(M1-t)+minAdm((t,)+M[2:]) for t in range(0,min(M0,M1)+1))
def tstars(M):
    M0,M1=M[0],M[1]
    vals=[((M0-t)*(M1-t)+minAdm((t,)+M[2:]),t) for t in range(0,min(M0,M1)+1)]
    m=min(v for v,_ in vals); return set(t for v,t in vals if v==m)
def dtm(M): return min(M[2:])
def tmw(M): return min(M[1:])
def red(u,M): return (u,)+M[2:]

# The cut where hGae/FACT is actually needed: STRICT shell 1<=j<r. The mountain peels at t*.
# Question A: binding (t in tstars) AND strict AND hcvg^hrange^hpiv -> any b>dtm ?
# Question B: strict AND hcvg^hrange^hpiv (ANY t) -> any b>dtm ? (does the SIGNATURE alone, no binding, suffice at strict?)
for maxw,arities in [(6,[4]),(6,[5]),(5,[6]),(6,[3,4,5])]:
    A_total=0;A_fail=0;A_samp=[]      # binding & strict & hyps
    B_total=0;B_fail=0;B_samp=[]      # strict & hyps (any t)
    for arity in arities:
        for M in itertools.product(range(1,maxw+1),repeat=arity):
            M0,M1=M[0],M[1]; rho=dtm(M); ml=M[-1]; tw=tmw(M); ts=tstars(M)
            for t in range(1,min(M0,M1)+1):
                r=min(M0-t,M1-t)
                for j in range(1,r):            # STRICT shell only
                    u=t+j;a=M0-u;b=M1-u
                    if a<0 or b<0: continue
                    if not (minAdm(red(u,M))<=u*tw): continue      # hpiv
                    if not (a+b<=min(M1,ml)-j): continue           # hcvg
                    if not (min(M1,ml)-j<=M[2]): continue          # hrange
                    B_total+=1
                    if b>rho:
                        B_fail+=1
                        if len(B_samp)<8: B_samp.append((M,t,j,u,a,b,rho,sorted(ts)))
                    if t in ts:
                        A_total+=1
                        if b>rho:
                            A_fail+=1
                            if len(A_samp)<8: A_samp.append((M,t,j,u,a,b,rho,sorted(ts)))
    lbl=",".join(map(str,arities))
    print(f"=== arity {lbl} widths 1..{maxw} (STRICT shells only, hcvg^hrange^hpiv) ===")
    print(f"  B: strict^hyps (ANY t): {B_total} cuts, b>dtm fails: {B_fail}")
    for s in B_samp: print(f"      B-fail M={s[0]} t={s[1]} j={s[2]} u={s[3]} a={s[4]} b={s[5]} dtm={s[6]} tstar={s[7]}")
    print(f"  A: strict^hyps^BINDING(t=t*): {A_total} cuts, b>dtm fails: {A_fail}")
    for s in A_samp: print(f"      A-fail M={s[0]} t={s[1]} j={s[2]} u={s[3]} a={s[4]} b={s[5]} dtm={s[6]} tstar={s[7]}")
