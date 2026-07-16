"""
Confirm the b=1 edge JOINT rank-sector = TWO chains (r=1 -> redChain u M, r=0 -> redChain (u+1) M),
both at exponent c'-a/2, both reaching c'<1/2minAdm(M) via cut-soundness. Exact-N, NO MC.
Sector charges: both codim a (D-cert corank-one tie) -> charge a/2. Reach conditions:
  r=1: a/2 + 1/2 minAdm(redChain u M)     >= 1/2 minAdm(M)   <=>  a + minAdm(redChain u M) >= minAdm(M)   [cut-sound u, peel=a]
  r=0: a/2 + 1/2 minAdm(redChain (u+1) M) >= 1/2 minAdm(M)   <=>  a + minAdm(redChain (u+1) M) >= minAdm(M) [peel(u+1)=0 => minAdm(rc_{u+1})>=minAdm(M), even stronger]
Also verify u+1=M1 is a valid cut (<= min(M0,M1)).
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
WMAX=7
cells=0; r1_fail=0; r0_fail=0; uplus1_invalid=0
for arity in (4,5):
    for M in product(range(1,WMAX+1),repeat=arity):
        M0,M1=M[0],M[1]
        u=M1-1
        if u<1 or u>min(M0,M1): continue
        a=M0-u
        if a<1 or not (a<u): continue
        rho=min(M[1:])
        if a+1 != rho+1:   # restrict to the TIE (edgefub's edge): a+b=rho+1, b=1 => a=rho
            continue
        cells+=1
        mM=minAdm(M)
        # r=1 chain: redChain u M ; r=0 chain: redChain (u+1) M
        rc1=redChain(u,M); rc0=redChain(u+1,M)
        if u+1 > min(M0,M1): uplus1_invalid+=1
        if not (a + minAdm(rc1) >= mM): r1_fail+=1
        if not (a + minAdm(rc0) >= mM): r0_fail+=1
print(f"b=1 TIE (a=rho) a<u edge cells (arity 4,5, widths<= {WMAX}): {cells}")
print(f"  u+1 invalid cut: {uplus1_invalid}  (expect 0)")
print(f"  r=1 sector (redChain u M) reach FAILS: {r1_fail}  (expect 0 = cut-soundness at u)")
print(f"  r=0 sector (redChain (u+1) M) reach FAILS: {r0_fail}  (expect 0)")
print("  => both sectors reach c'<1/2minAdm(M); two-chain joint rank-sector CLEAN (tie-log = harmless multiplicity)" if (r1_fail==0 and r0_fail==0 and uplus1_invalid==0) else "  => RECHECK")
