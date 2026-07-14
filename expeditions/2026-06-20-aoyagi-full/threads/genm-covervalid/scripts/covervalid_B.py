from functools import lru_cache
from itertools import product
def sub(x,y): return x-y if x>y else 0
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def redChain(u,M): return (u,)+tuple(M[2:])
def achievers(M):
    best=minAdm(M)
    return [u for u in range(min(M[0],M[1])+1) if (M[0]-u)*(M[1]-u)+minAdm(redChain(u,M))==best]
def tMW(M): return min(M[1:])
def hpiv_ok(M,u): return minAdm(redChain(u,M))<=u*tMW(M)

RANGES=[(range(1,9),3),(range(1,9),4),(range(1,7),5)]
# CONSISTENT refinement (B): t* = greatest achiever>=1; good = hpiv at all genuine nonempty shells wrt THIS t*.
fail=[]; good=0; degenerate_r0=0; seen=set()
for rng,length in RANGES:
    for M in product(rng,repeat=length):
        if M in seen: continue
        seen.add(M)
        cuts=[t for t in achievers(M) if t>=1]
        if not cuts: continue
        t=max(cuts)
        M0,M1,M2,Mlast=M[0],M[1],M[2],M[-1]
        r=min(sub(M0,t),sub(M1,t)); Lam=min(M1,Mlast)
        # good gate wrt this t*
        isgood=True
        for j in range(0,r+1):
            u=t+j; a=sub(M0,u); b=sub(M1,u); m=sub(Lam,j)
            if m<=M2 and a>=1 and b>=1 and not hpiv_ok(M,u): isgood=False
        if not isgood: continue
        good+=1
        # any genuine nonempty shell?
        hasgenuine=False
        for j in range(0,r+1):
            u=t+j; a=sub(M0,u); b=sub(M1,u); m=sub(Lam,j)
            if m<=M2 and a>=1 and b>=1:
                hasgenuine=True
                if not(a+b<=m): fail.append((M,t,j,a,b,m))
        if not hasgenuine: degenerate_r0+=1
print(f"Refinement (B) consistent [t*=GREATEST achiever]:")
print(f"  good chains: {good}   hcvg-FAIL at any genuine nonempty shell: {len(fail)}   {fail[:6]}")
print(f"  good chains with NO genuine shell (r collapses, front peel charge 0 corner): {degenerate_r0}")
print()
# Compare: how many good chains have >1 achiever (plateau) -> where least vs greatest differ
multi=0; least_ne_greatest_sectorfix=0; seen=set()
for rng,length in RANGES:
    for M in product(rng,repeat=length):
        if M in seen: continue
        seen.add(M)
        cuts=[t for t in achievers(M) if t>=1]
        if not cuts: continue
        if len(cuts)>1: multi+=1
print(f"good/eligible chains with a minAdm-achiever PLATEAU (|achievers>=1|>1): {multi}")
