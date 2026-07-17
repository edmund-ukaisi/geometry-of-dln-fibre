"""
Is the a=0/b=0 WING front rank-sector uniformly RANK-1 (jointpnp's min(r,k)<=1), or does it have
general-r,k (>=2) strata? For a wing at cut t=min(M0,M1), the front rank-sector strata s in [0,t] reduce
to redChain s M at charge (M0-s)(M1-s). Two questions:
 (1) BINDING stratum s*: is min(M0-s*, M1-s*) <= 1 always? (i.e. is the tight/threshold-setting stratum rank-1?)
 (2) Do NON-binding strata with min(M0-s, M1-s) >= 2 occur (part of the atlas, even if not binding)?
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

bind_rank_gt1=0; wing_tot=0; nonbind_rk2_exists=0; bind_examples=[]
for M in gen([4,5],6):
    if len(M)<3: continue
    M0,M1=M[0],M[1]
    t=min(M0,M1)                      # wing cut (deepest)
    # is this a POWER wing? d=0 (a=0 or b=0), and the front rank-sector nontrivial
    a=M0-t; b=M1-t
    if min(a,b)!=0: continue           # wing = d=0
    wing_tot+=1
    mA=minAdmRec(M)
    strata=[(s,(M0-s)*(M1-s)+minAdmRec(redChain(s,M))) for s in range(0,t+1)]
    binding=[s for (s,val) in strata if val==mA]
    sstar=min(binding)                 # smallest binding s (tightest charge)
    # rank of the binding stratum block = min(M0-s*, M1-s*)
    bind_rank=min(M0-sstar, M1-sstar)
    if bind_rank>1:
        bind_rank_gt1+=1
        if len(bind_examples)<8: bind_examples.append((M,sstar,bind_rank,f"minAdm={mA}"))
    # do non-binding strata with min(M0-s,M1-s)>=2 occur among 0<s<t?
    if any(min(M0-s,M1-s)>=2 for s in range(0,t+1)):
        nonbind_rk2_exists+=1
print("WING (d=0) cells:", wing_tot)
print("(1) BINDING stratum rank min(M0-s*,M1-s*) > 1 [general-r,k binding]:", bind_rank_gt1, "/", wing_tot)
for e in bind_examples: print("   binding-rank>1:", e)
print("(2) cells with SOME stratum min(M0-s,M1-s)>=2 (general-r,k in the atlas, binding or not):", nonbind_rk2_exists, "/", wing_tot)
