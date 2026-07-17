"""
Is d1 a<u buildable NOW? Its w=frobSq(X·Q) part (X=[P|B12], u x M1, u=t) reduces to redChain u M=(u,M2,...)
via the frontCollapse atom (collapse (u,M1)->(u,M2) via X·A1). Regime: BOUNDED (M2<=b) uses the LANDED
frontCollapse_wide_bounded_lt_top; POWER (M2>=b+2) needs the HELD joint-coupled; LOG (M2=b+1) delta-fold.
Here the front excess is M1-u = M1-t = b (the corank col dim). So bounded-w iff M2 <= b.
Count the d1 a<u subset that is bounded-w (buildable now). minAdmRec from RouteMLayerSplit.lean.
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
cat=Counter()
for M in gen([4,5],6):
    if len(M)<3: continue
    M0,M1=M[0],M[1]; M2=M[2]
    for t in range(1,min(M0,M1)+1):
        a=M0-t; b=M1-t; d=min(a,b); u=t
        if d!=1: continue
        if a>=u: continue     # a<u arm
        # pivot-front excess = M1-u = b ; bounded-w iff M2<=b
        if M2<=b: cat['bounded-w (M2<=b): LANDED atom, BUILDABLE NOW']+=1
        elif M2==b+1: cat['LOG-w (M2=b+1): coupled log-density delta-fold']+=1
        else: cat['POWER-w (M2>=b+2): HELD joint-coupled']+=1
print("d1 a<u cut census by pivot-front-collapse regime (arity 4,5, w<=6):")
for k,v in sorted(cat.items()): print(f"   {v:5d}  {k}")
print()
print("NOTE: w=frobSq(X·Q), X=[P|B12] u x M1 (u=t), front excess M1-u=b. So the SAME frontCollapse atom as a=0")
print("(just m=u instead of m=M0). d1 a<u is NOT direct-to-hIH: it consumes the frontCollapse atom.")
print("BUILDABLE NOW = the bounded-w subset (M2<=b): landed frontCollapse_wide_bounded_lt_top + corner_block")
print("(a<u, joint sphere) + scaledRadialEuclid. POWER-w waits for the joint-coupled mechanism.")
