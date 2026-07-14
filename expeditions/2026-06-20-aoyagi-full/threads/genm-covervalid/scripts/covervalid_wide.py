# Wider sweep (widths up to 8 for arity 3,4; up to 6 for arity 5): firm up
#   (A) off-sector j in [1,r-1]:  hpiv  =>  hcvg   (obstruction claim)
#   (B) sector j=0: characterize when hcvg holds/fails.
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
def dTM(M): return min(M[2:])
def hpiv_ok(M,u): return minAdm(redChain(u,M))<=u*tMW(M)

RANGES=[(range(1,9),3),(range(1,9),4),(range(1,7),5)]
offfail=[]; offcount=0
# sector characterization: does hcvg(0) <=> (a*+b* <= min(M1,Mlast)) match "front-heavy or M0<=... " ?
seen=set()
for rng,length in RANGES:
    for M in product(rng,repeat=length):
        if M in seen: continue
        seen.add(M)
        M0,M1,M2,Mlast=M[0],M[1],M[2],M[-1]
        t=bindingCut(M)
        if t<1: continue
        r=min(sub(M0,t),sub(M1,t)); Lam=min(M1,Mlast)
        for j in range(1,r):                     # genuine off-sector 1<=j<=r-1
            u=t+j; a=sub(M0,u); b=sub(M1,u)
            if a<1 or b<1: continue
            m=sub(Lam,j)
            if not (m<=M2): continue
            offcount+=1
            hcvg=(a+b<=m); hpiv=hpiv_ok(M,u)
            if hpiv and not hcvg:
                offfail.append((M,t,j,u,a,b,m))
print(f"OFF-SECTOR (1<=j<=r-1), genuine+nonempty: {offcount} shells")
print(f"  good(hpiv) & hcvg-FAIL: {len(offfail)}   {offfail[:8]}")
print()
# SECTOR j=0 characterization
astar_gt=0; total0=0; hcvgfail0=0
examples=[]
seen=set()
for rng,length in [(range(1,9),3),(range(1,8),4)]:
    for M in product(rng,repeat=length):
        if M in seen: continue
        seen.add(M)
        M0,M1,M2,Mlast=M[0],M[1],M[2],M[-1]
        t=bindingCut(M)
        if t<1: continue
        a=sub(M0,t); b=sub(M1,t)
        if a<1 or b<1: continue
        Lam=min(M1,Mlast); m=Lam
        if not (m<=M2): continue
        total0+=1
        hcvg=(a+b<=Lam)
        if not hcvg: hcvgfail0+=1
print(f"SECTOR j=0 genuine+nonempty: {total0};  hcvg-FAIL: {hcvgfail0}  ({100*hcvgfail0//max(total0,1)}%)")
print("  hcvg(0) <=> a*+b* <= min(M1,Mlast), where a*=M0-t*, b*=M1-t*.")
print()
# Is off-sector obstruction really hpiv, or does non-waist(dTM<=M1) also suffice/needed? cross-check
import itertools
mismatch=0
seen=set()
for rng,length in [(range(1,8),3),(range(1,7),4)]:
    for M in product(rng,repeat=length):
        if M in seen: continue
        seen.add(M)
        M0,M1,M2,Mlast=M[0],M[1],M[2],M[-1]
        t=bindingCut(M)
        if t<1: continue
        r=min(sub(M0,t),sub(M1,t)); Lam=min(M1,Mlast)
        for j in range(1,r):
            u=t+j; a=sub(M0,u); b=sub(M1,u)
            if a<1 or b<1: continue
            m=sub(Lam,j)
            if not(m<=M2): continue
            hcvg=(a+b<=m); nonwaist=(dTM(M)<=M1)
            if nonwaist and not hcvg:
                mismatch+=1
                if mismatch<=8: print("   NONWAIST(dTM<=M1) off-sector hcvg FAIL:",M,"t*",t,"j",j,"a",a,"b",b,"m",m)
print(f"off-sector: nonwaist(dTM<=M1) & hcvg-FAIL count: {mismatch}")
