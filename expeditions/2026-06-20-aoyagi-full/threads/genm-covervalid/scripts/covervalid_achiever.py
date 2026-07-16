# Does the GREATEST binding-cut achiever fix hcvg at the sector (and all genuine shells)?
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
    return [u for u in range(min(M[0],M[1])+1)
            if (M[0]-u)*(M[1]-u)+minAdm(redChain(u,M))==best]
def tMW(M): return min(M[1:])
def hpiv_ok(M,u): return minAdm(redChain(u,M))<=u*tMW(M)

def shells_all_hcvg(M,t):
    """with binding cut t: do ALL genuine non-empty shells satisfy hcvg? report (allpass, sector_hcvg)."""
    M0,M1,M2,Mlast=M[0],M[1],M[2],M[-1]
    r=min(sub(M0,t),sub(M1,t)); Lam=min(M1,Mlast)
    allpass=True; sector=None
    for j in range(0,r+1):
        u=t+j; a=sub(M0,u); b=sub(M1,u); m=sub(Lam,j)
        if not (m<=M2): continue        # non-empty only
        if a<1 or b<1: continue          # genuine only
        hcvg=(a+b<=m)
        if j==0: sector=hcvg
        if not hcvg: allpass=False
    return allpass,sector

RANGES=[(range(1,9),3),(range(1,9),4),(range(1,7),5)]
# For chains that are GOOD (hpiv holds at all genuine nonempty shells wrt the LEAST cut),
# test: does the LEAST cut give all-hcvg? does the GREATEST? does SOME achiever?
cnt=Counter=__import__('collections').Counter()
least_allpass=0; greatest_allpass=0; some_allpass=0; none_allpass=0; goodchains=0
fail_greatest=[]
seen=set()
for rng,length in RANGES:
    for M in product(rng,repeat=length):
        if M in seen: continue
        seen.add(M)
        cuts=achievers(M)
        cuts=[t for t in cuts if t>=1]
        if not cuts: continue
        least=min(cuts); greatest=max(cuts)
        # good = hpiv holds at all genuine nonempty shells at the LEAST cut (Lean's bindingCut)
        M0,M1,M2,Mlast=M[0],M[1],M[2],M[-1]
        r=min(sub(M0,least),sub(M1,least)); Lam=min(M1,Mlast)
        good=True
        for j in range(0,r+1):
            u=least+j; a=sub(M0,u); b=sub(M1,u); m=sub(Lam,j)
            if m<=M2 and a>=1 and b>=1 and not hpiv_ok(M,u): good=False
        if not good: continue
        goodchains+=1
        la,_=shells_all_hcvg(M,least)
        ga,_=shells_all_hcvg(M,greatest)
        sa=any(shells_all_hcvg(M,t)[0] for t in cuts)
        least_allpass+=la; greatest_allpass+=ga; some_allpass+=sa
        if not sa: none_allpass+=1
        if not ga and sum(M)<=11:
            fail_greatest.append((M,cuts,greatest))
print(f"GOOD chains (arity3-5, sweep): {goodchains}")
print(f"  ALL genuine-nonempty shells hcvg-pass with LEAST cut (=Lean bindingCut): {least_allpass}")
print(f"  ... with GREATEST achiever cut:                                          {greatest_allpass}")
print(f"  ... with SOME achiever cut:                                              {some_allpass}")
print(f"  ... with NO achiever cut (genuinely uncoverable by any binding cut):     {none_allpass}")
print()
print(f"good chains where GREATEST achiever still fails some genuine shell (small): {len(fail_greatest)}")
for M,cuts,g in fail_greatest[:15]:
    M0,M1,M2,Mlast=M[0],M[1],M[2],M[-1]
    print(f"   M={M} achievers={cuts} greatest={g}  ", end="")
    r=min(sub(M0,g),sub(M1,g)); Lam=min(M1,Mlast)
    fails=[]
    for j in range(0,r+1):
        u=g+j;a=sub(M0,u);b=sub(M1,u);m=sub(Lam,j)
        if m<=M2 and a>=1 and b>=1 and not(a+b<=m): fails.append((j,a,b,m))
    print("failing shells (j,a,b,m):",fails)
