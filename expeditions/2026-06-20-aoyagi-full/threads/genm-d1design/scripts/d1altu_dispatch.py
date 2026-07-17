"""
DEFINITIVE d1-a<u dispatch for d1altu. Two axes:
 (α) c' vs ½minAdm(redChain t M): drop-WHOLE-corank (charge 0) -> frontCollapse(X) at c' -> hIH(redChain t M),
     closes iff c' < ½minAdm(redChain t M). If minAdm(redChain t M) >= minAdm(M), the drop-whole-corank covers
     ALL c'<½minAdm(M) (α-high VACUOUS, no heart needed). Else α-high = keep-corank = heart's rank-1 leaf.
 (β) M₂ vs b (=M1-t): frontCollapse regime — M2<=b LANDED / M2=b+1 LOG / M2>=b+2 #2-POWER (heart).
Census the (α,β) combinations. minAdmRec from RouteMLayerSplit.lean.
"""
from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def mA(M):
    n=len(M)
    if n<=1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+mA((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))
def rc(t,M): return (t,)+M[2:]
def gen(ar,w):
    for L in ar:
        for M in product(range(1,w+1),repeat=L): yield M

from collections import Counter
alpha_high_reachable=0; tot=0; cat=Counter()
for M in gen([4,5],6):
    if len(M)<3: continue
    M0,M1=M[0],M[1]; M2=M[2]
    for t in range(1,min(M0,M1)+1):
        a=M0-t; b=M1-t; d=min(a,b); u=t
        if d!=1 or a>=u: continue
        tot+=1
        mAM=mA(M); mARC=mA(rc(t,M))
        # (α) is α-high (c' in [½mARC, ½mAM)) reachable? iff mARC < mAM
        alpha_high = (mARC < mAM)
        if alpha_high: alpha_high_reachable+=1
        # (β) frontCollapse regime
        if M2<=b: beta='M2<=b LANDED'
        elif M2==b+1: beta='M2=b+1 LOG'
        else: beta='M2>=b+2 POWER(#2/heart)'
        # combined status of the DROP-WHOLE-corank branch (α-low):
        #   clean-now if M2<=b; LOG if b+1; heart-gated(#2) if >=b+2
        # plus α-high (if reachable) = heart's rank-1 leaf (held)
        key=(beta, 'α-high reachable(heart rank-1)' if alpha_high else 'α-high vacuous (drop-corank covers all)')
        cat[key]+=1
print("d1 a<u cuts:", tot)
print("α-high (keep-corank=heart rank-1) REACHABLE [minAdm(redChain t M) < minAdm(M)]:", alpha_high_reachable, "/", tot)
print("   (if 0: d1-a<u is ALWAYS drop-whole-corank; heart rank-1 leaf never needed for d1-a<u — only #2 via frontCollapse-POWER)")
print()
print("(α-low drop-whole-corank β-regime) × (α-high reachability) census:")
for k,v in sorted(cat.items()): print(f"   {v:5d}  {k}")
