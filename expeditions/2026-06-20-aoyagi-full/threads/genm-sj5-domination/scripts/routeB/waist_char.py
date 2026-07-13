from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def binding_cuts(M):
    mA=minAdm(M)
    return [t for t in range(min(M[0],M[1])+1)
            if (M[0]-t)*(M[1]-t)+minAdm((t,)+tuple(M[2:]))==mA]
def rho(M): return min(M[1:])
def rev(M): return tuple(reversed(M))
def piv_strict(M):
    r=rho(M)
    for t in binding_cuts(M):
        if t>=1 and t*r<minAdm((t,)+tuple(M[2:])): return False
        for j in range(1,min(M[0]-t,M[1]-t)+1):
            u=t+j;a=M[0]-u;b=M[1]-u
            if a<1 or b<1: continue
            if u*r<minAdm((u,)+tuple(M[2:])): return False
    return True

# 3-width: is "both-ends-bad" EXACTLY the strict-waist set {w<M0 and w<M2}?
print("3-width chains (widths 1..8): both-ends-bad  vs  strict-waist (M1<M0 and M1<M2)")
mism=0; both=0; waist=0
for M in product(range(1,9),repeat=3):
    bb = not piv_strict(M) and not piv_strict(rev(M))
    w  = M[1]<M[0] and M[1]<M[2]
    if bb: both+=1
    if w: waist+=1
    if bb!=w: 
        mism+=1
        if mism<=10: print("   MISMATCH", M, "bothbad=",bb,"waist=",w)
print(f"  both-ends-bad: {both} | strict-waist: {waist} | mismatches: {mism}")

# so for 3-width, front-good-from-an-end  <=>  NOT strict-waist  <=>  monotone-ish (M1>=M0 or M1>=M2)
# sanity: a chain is fine iff it is NOT a strict interior-minimum at position 1
