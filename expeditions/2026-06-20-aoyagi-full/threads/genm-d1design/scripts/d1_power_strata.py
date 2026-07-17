"""
POWER-case (a=0 wide, M2>=b+2) front rank-sector: pin the charge-vs-codim structure per stratum s,
to ground the N3 Jacobian derivation. minAdmRec from RouteMLayerSplit.lean.
For the wing at cut t=M0 (a=0), stratum s in [0,M0] reduces to redChain s M=(s,M2,...) at
peelCharge (M0-s)(M1-s). Compare to:
  - Wrank codim (M0-s)(M2-s)   [codim {rank(W)=s} in M0xM2 matrices]
  - density order A_s          [satred's per-stratum, if a single-number model]
to see whether charge = codim (only when M1=M2) and expose the true per-stratum exponent.
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

# smallest non-degenerate POWER wing witnesses + the binding stratum
print("wing a=0 POWER witnesses (M0<M1, M2>=M1-M0+2): binding stratum s* + charge vs Wrank-codim")
for M in [(2,3,4),(2,3,5),(2,4,5),(3,4,6),(2,3,3),(1,2,3)]:
    M0,M1,M2=M[0],M[1],M[2]
    if not (M0<M1 and M2>=M1-M0+2):
        print(f"  {M}: (not strict POWER; b={M1-M0}, need M2>={M1-M0+2})")
    mA=minAdmRec(M)
    terms=[]
    for s in range(0,M0+1):
        charge=(M0-s)*(M1-s)
        val=charge+minAdmRec(redChain(s,M))
        terms.append((s,charge,minAdmRec(redChain(s,M)),val))
    sstar=min(terms,key=lambda x:x[3])
    s,charge,redm,val=sstar
    wrank_codim=(M0-s)*(M2-s)
    print(f"  M={M}: minAdm={mA}, binding s*={s} charge(M0-s)(M1-s)={charge} redChain{redChain(s,M)} minAdm={redm} sum={val}"
          f"  | Wrank-codim(M0-s)(M2-s)={wrank_codim}  {'==charge' if wrank_codim==charge else 'NE charge (M1!=M2)'}")

# arity-4 wing POWER cells: is the binding stratum s* INTERIOR (0<s*<M0, genuinely-new blow-up) or edge?
from collections import Counter
dist=Counter(); interior_ex=[]
for L in [4]:
    for M in product(range(1,7),repeat=L):
        M0,M1,M2=M[0],M[1],M[2]
        if not (M0<M1 and M2>=M1-M0+2): continue   # strict POWER wing
        mA=minAdmRec(M)
        terms=[(s,(M0-s)*(M1-s)+minAdmRec(redChain(s,M))) for s in range(0,M0+1)]
        sstar=min(t[0] for t in terms if t[1]==mA)   # smallest binding s
        # classify binding position
        if sstar==0: cat='edge s=0'
        elif sstar==M0: cat='edge s=M0'
        else: cat='INTERIOR 0<s<M0'
        dist[cat]+=1
        if cat=='INTERIOR 0<s<M0' and len(interior_ex)<6:
            interior_ex.append((M,sstar,(M0-sstar)*(M1-sstar),redChain(sstar,M),minAdmRec(redChain(sstar,M))))
print()
print("arity-4 wing POWER binding-stratum distribution:", dict(dist))
for e in interior_ex: print("   INTERIOR:", e)
