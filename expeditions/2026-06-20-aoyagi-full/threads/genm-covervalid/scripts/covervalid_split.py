# Split j=0 (SECTOR/top stratum) from j>=1 (OFF-SECTOR), over GENUINE (a>=1,b>=1) non-empty shells.
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
def tailMinWidth(M): return min(M[1:])
def deepTailMin(M): return min(M[2:])
def hpiv_ok(M,u): return minAdm(redChain(u,M)) <= u*tailMinWidth(M)

RANGES=[(range(1,8),3),(range(1,7),4),(range(1,6),5)]

from collections import Counter
c0=Counter(); c1=Counter()          # keyed by (hcvg,hpiv), j=0 and j>=1
w0=[]; w1=[]                          # good(hpiv)-case hcvg-fail witnesses
seen=set()
for rng,length in RANGES:
    for M in product(rng,repeat=length):
        if M in seen: continue
        seen.add(M)
        M0,M1,M2,Mlast=M[0],M[1],M[2],M[-1]
        tstar=bindingCut(M)
        if tstar<1: continue
        r=min(sub(M0,tstar),sub(M1,tstar)); Lam=min(M1,Mlast)
        for j in range(0,r+1):
            u=tstar+j; a=sub(M0,u); b=sub(M1,u)
            if a<1 or b<1: continue
            m=sub(Lam,j)
            if not (m<=M2): continue           # hrange: non-empty only
            hcvg=(a+b<=m); hpiv=hpiv_ok(M,u)
            if j==0:
                c0[(hcvg,hpiv)]+=1
                if hpiv and not hcvg: w0.append((M,tstar,j,u,a,b,m))
            else:
                c1[(hcvg,hpiv)]+=1
                if hpiv and not hcvg: w1.append((M,tstar,j,u,a,b,m))

print("=== j = 0  (SECTOR / top stratum) : (hcvg,hpiv) -> count ===")
for k,n in sorted(c0.items()): print(f"    hcvg={k[0]!s:5} hpiv={k[1]!s:5} : {n}")
print(f"  GOOD-case (hpiv) hcvg-FAIL at j=0: {len(w0)}  e.g. {w0[:6]}")
print()
print("=== j >= 1 (OFF-SECTOR) : (hcvg,hpiv) -> count ===")
for k,n in sorted(c1.items()): print(f"    hcvg={k[0]!s:5} hpiv={k[1]!s:5} : {n}")
print(f"  GOOD-case (hpiv) hcvg-FAIL at j>=1: {len(w1)}")
for w in w1[:25]:
    M,tstar,j,u,a,b,m=w
    print(f"    M={M} t*={tstar} j={j} u={u} a={a} b={b} m={m} a+b={a+b}  M2={M[2]} M1={M[1]} Mlast={M[-1]} deepTailMin={deepTailMin(M)}")
print()
# Classify specific anchors
print("=== anchor classification ===")
for M in [(3,3,3),(2,2,2),(3,4,4),(4,3,5,5),(4,3,5,2),(3,3,4,4),(4,4,2,2),(3,3,2,2)]:
    tstar=bindingCut(M); r=min(sub(M[0],tstar),sub(M[1],tstar)); Lam=min(M[1],M[-1])
    # is chain "good" per hpiv at all nonempty genuine shells?
    good=True
    for j in range(0,r+1):
        u=tstar+j; a=sub(M[0],u); b=sub(M[1],u)
        if a<1 or b<1: continue
        m=sub(Lam,j)
        if m<=M[2] and not hpiv_ok(M,u): good=False
    print(f"  M={M}: minAdm={minAdm(M)} t*={tstar} r={r} min(M1,Mlast)={Lam} "
          f"good(hpiv)={good} deepTailMin<=M1={deepTailMin(M)<=M[1]}")
