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

# reversal minAdm-invariance (should hold by perm-invariance; sanity check)
bad=0
for Ln in [3,4,5,6]:
    for M in product(range(1,7),repeat=Ln):
        if minAdm(M)!=minAdm(rev(M)): bad+=1
print("minAdm(M) != minAdm(rev M) count (expect 0):", bad)

# (2,1,2) under 3 conventions
def piv_bind_only(M):   # ONLY binding-cut main pivot j=0
    r=rho(M)
    for t in binding_cuts(M):
        if t>=1 and t*r<minAdm((t,)+tuple(M[2:])): return False
    return True
def piv_strict(M):      # binding j=0 + proper off-sectors a,b>=1
    r=rho(M)
    for t in binding_cuts(M):
        if t>=1 and t*r<minAdm((t,)+tuple(M[2:])): return False
        for j in range(1,min(M[0]-t,M[1]-t)+1):
            u=t+j;a=M[0]-u;b=M[1]-u
            if a<1 or b<1: continue
            if u*r<minAdm((u,)+tuple(M[2:])): return False
    return True
def piv_allu(M):        # all u in [t*, min(M0,M1)]
    r=rho(M)
    for t in binding_cuts(M):
        for u in range(t,min(M[0],M[1])+1):
            if u<1: continue
            if u*r<minAdm((u,)+tuple(M[2:])): return False
    return True

for name,fn in [("bind-only",piv_bind_only),("strict",piv_strict),("all-u",piv_allu)]:
    bb=[M for Ln in [3,4,5,6] for M in product(range(1,7),repeat=Ln)
        if not fn(M) and not fn(rev(M))]
    print(f"[{name:10s}] both-ends-bad: {len(bb)} | (2,1,2) bad both ends: {(2,1,2) in bb}")

# characterization: minimal counterexample family = (k,1,k), (k,2,k)? and (a,c,b) waist
print("\nSmallest waist counterexamples (strict conv), grouped:")
canon=sorted(set(min(M,rev(M)) for Ln in [3] for M in product(range(1,7),repeat=Ln)
    if not piv_strict(M) and not piv_strict(rev(M))), key=lambda M:(sum(M),M))
print("  3-width both-ends-bad (up to reversal):", canon)
