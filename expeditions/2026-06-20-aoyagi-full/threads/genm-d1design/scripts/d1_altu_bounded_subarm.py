"""
Does d1-a<u have a CLEAN c'<=a/2 bounded sub-arm (drop WHOLE corank -> frontCollapse(X) at charge 0)?
The bounded branch: freedSchurLoss >= W (C,Gamma-free) => integrand <= W^{-c'}, corank -> bounded vol,
-> frontCollapse(X=[P|B12], u x M1) at exponent c', reducing to hIH(redChain u M) at threshold c'<½minAdm(redChain u M).
CLEAN sub-arm covering c'<=a/2 requires:
  (i)  CHARGE: a/2 <= ½minAdm(redChain u M), i.e. a <= minAdm(redChain u M)  [c'<=a/2 within frontCollapse threshold]
  (ii) frontCollapse(X) is the LANDED bounded atom: M2 <= b (=M1-u), else frontCollapse itself is POWER (heart).
If (i)&(ii): CLEAN c'<=a/2 sub-arm + HEART c'>a/2. If not (i): charge gap. If not (ii): bounded branch's
frontCollapse is POWER -> folds into heart.
minAdmRec from RouteMLayerSplit.lean.
"""
from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdmRec(M):
    n=len(M)
    if n<=1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))
def redChain(t,M): return (t,)+M[2:]
def gen(ar,w):
    for L in ar:
        for M in product(range(1,w+1),repeat=L): yield M

from collections import Counter
tot=0; charge_ok=0; charge_fail=[]; fc_bounded=0; both=0
cat=Counter()
for M in gen([4,5],6):
    if len(M)<3: continue
    M0,M1,M2=M[0],M[1],M[2]
    for t in range(1,min(M0,M1)+1):
        a=M0-t; b=M1-t; d=min(a,b); u=t
        if d!=1 or a>=u: continue   # d1 a<u
        tot+=1
        rc=redChain(u,M); mRC=minAdmRec(rc)
        ci = (a <= mRC)                 # (i) charge covers c'<=a/2
        cii = (M2 <= b)                 # (ii) frontCollapse bounded (landed)
        if ci: charge_ok+=1
        else:
            if len(charge_fail)<6: charge_fail.append((M,t,f"a={a} > minAdm(redChain {rc})={mRC}"))
        if cii: fc_bounded+=1
        if ci and cii: both+=1
        # classify
        if ci and cii: cat['CLEAN c<=a/2 sub-arm (landed) + heart c>a/2']+=1
        elif ci and not cii: cat['charge-ok but frontCollapse POWER (bounded branch folds to heart)']+=1
        elif (not ci) and cii: cat['frontCollapse bounded but charge gap (a>minAdm redChain)']+=1
        else: cat['neither: folds to heart']+=1
print("d1 a<u cuts:", tot)
print("(i) charge a<=minAdm(redChain u M) [c'<=a/2 within threshold]:", charge_ok, "/", tot, "  fails:", tot-charge_ok)
for e in charge_fail: print("   charge-fail:", e)
print("(ii) frontCollapse bounded M2<=b [landed clean atom]:", fc_bounded, "/", tot)
print("(i)&(ii) genuinely CLEAN c'<=a/2 sub-arm:", both, "/", tot)
print("census:", dict(cat))
