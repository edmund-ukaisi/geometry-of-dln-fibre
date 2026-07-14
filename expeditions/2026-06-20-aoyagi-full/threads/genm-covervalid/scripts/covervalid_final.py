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
def bindingCut(M):
    best=minAdm(M)
    for u in range(min(M[0],M[1])+1):
        if (M[0]-u)*(M[1]-u)+minAdm(redChain(u,M))==best: return u
def tMW(M): return min(M[1:])
def hpiv_ok(M,u): return minAdm(redChain(u,M))<=u*tMW(M)

RANGES=[(range(1,9),3),(range(1,9),4),(range(1,7),5)]
# For each shell class, count good-case (hpiv) hcvg pass/fail.  "good" = per-shell hpiv holds.
from collections import Counter
res={'sector(j=0)':Counter(),'offsector(1<=j<=r-1)':Counter(),'saturated/degenerate(j=r)':Counter()}
smallest_sector=None
seen=set()
for rng,length in RANGES:
    for M in product(rng,repeat=length):
        if M in seen: continue
        seen.add(M)
        M0,M1,M2,Mlast=M[0],M[1],M[2],M[-1]
        t=bindingCut(M)
        if t<1: continue
        r=min(sub(M0,t),sub(M1,t)); Lam=min(M1,Mlast)
        for j in range(0,r+1):
            u=t+j; a=sub(M0,u); b=sub(M1,u); m=sub(Lam,j)
            hrange=(m<=M2)
            if not hrange: continue
            genuine=(a>=1 and b>=1)
            hcvg=(a+b<=m); hpiv=hpiv_ok(M,u)
            if j==0 and genuine:
                cls='sector(j=0)'
            elif genuine and 1<=j<=r-1:
                cls='offsector(1<=j<=r-1)'
            else:
                cls='saturated/degenerate(j=r)'
            if hpiv:
                res[cls]['pass' if hcvg else 'FAIL']+=1
                if cls=='sector(j=0)' and not hcvg and smallest_sector is None and sum(M)<=9:
                    smallest_sector=(M,t,a,b,m)
print("GOOD-case (hpiv) hcvg over shell classes  [pass / FAIL]:")
for cls,c in res.items():
    print(f"  {cls:28}: pass={c['pass']:5}  FAIL={c['FAIL']:5}")
print()
print("Smallest good-case sector(j=0) hcvg witness:", smallest_sector)
print()
# Principled balanced-cube family (w,w,w): show hcvg(sector) boundary at w
print("Balanced cube (w,w,w): t*, a*+b*, min(M1,Mlast), hcvg(sector j=0):")
for w in range(2,8):
    M=(w,w,w); t=bindingCut(M); a=sub(w,t);b=sub(w,t); Lam=min(w,w)
    print(f"   w={w}: minAdm={minAdm(M)} t*={t} a*+b*={a+b} Lam={Lam} hcvg0={(a+b)<=Lam}  hpiv0={hpiv_ok(M,t)}")
