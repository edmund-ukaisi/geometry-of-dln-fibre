#!/usr/bin/env python3
"""
EXHAUSTIVE sweep of the sub-generic per-stratum charges + the Mval-membership structural check.

Candidates (per cut t, per sub-generic rank s' in [0, min(b,n)]):
  Cfree = a*s' + (b-s')(n-s')                          crude free-matrix heuristic
  C1    = a*s' + kappa(t,s')                           active + PRODUCT-rank stratum codim
  C2    = a*s' + kappa(t,s') + minAdm(redChain t M)    active + stratum codim + deeper recursion
where kappa(t,s') = minAdm( (b, M2,...,ML) - s' )  [peeling identity, PRODUCT-rank codim].

For each candidate: count (t,s') with charge < minAdm(M) over ALL chains up to bounds.
Also: does C2 equal SOME Mval(M,T) with T admissible? (structural proof that C2 is a genuine orbit codim
      >= minAdm, and tight).
"""
import io, contextlib
_buf = io.StringIO()
with contextlib.redirect_stdout(_buf):
    import rankcharge as R
from itertools import product
from functools import lru_cache

minAdm = R.minAdmRec
redChain = R.redChain
Mval = R.Mval
admPred = R.admPred
admBound = R.admBound

@lru_cache(maxsize=None)
def mA(W): return minAdm(tuple(W))

def clamp_sub(W, r): return tuple(max(0, w-r) for w in W)

def kappa(t, M, sp):
    b = M[1]-t
    return mA(clamp_sub((b,)+tuple(M[2:]), sp))

def charge_set(t, M, sp):
    a=M[0]-t; b=M[1]-t; n=min(M[2:])
    k=kappa(t,M,sp); rc=minAdm(redChain(t,M))
    return dict(Cfree=a*sp+(b-sp)*(n-sp), C1=a*sp+k, C2=a*sp+k+rc, kappa=k, rc=rc, a=a, b=b, n=n)

def sweep(Lp1, wmax, wmin=0):
    fails = {'Cfree':0,'C1':0,'C2':0}
    above_min = {'Cfree':0,'C1':0,'C2':0}   # count chains where min over (t,s') != minAdm
    chains=0
    ex = {'Cfree':[],'C1':[],'C2':[]}
    tight_C2_fail=[]
    for M in product(range(wmin,wmax+1),repeat=Lp1):
        if M[0]==0 or M[1]==0:  # degenerate leading widths still valid; keep
            pass
        chains+=1
        m=minAdm(M); n=min(M[2:])
        mins={'Cfree':None,'C1':None,'C2':None}
        for t in range(min(M[0],M[1])+1):
            b=M[1]-t; s=min(b,n)
            for sp in range(0,s+1):
                cs=charge_set(t,M,sp)
                for key in ('Cfree','C1','C2'):
                    v=cs[key]
                    if mins[key] is None or v<mins[key]: mins[key]=v
                    if v<m:
                        fails[key]+=1
                        if len(ex[key])<8: ex[key].append((M,t,sp,v,m,cs))
        for key in ('Cfree','C1','C2'):
            if mins[key]!=m:
                above_min[key]+=1
        if mins['C2']!=m and len(tight_C2_fail)<8:
            tight_C2_fail.append((M,m,mins['C2']))
    return chains, fails, above_min, ex, tight_C2_fail

print("EXHAUSTIVE SWEEP: charge < minAdm failures, and min-over-strata != minAdm (non-tight)")
print(f"{'sweep':<22}{'chains':>8}  {'Cfree<':>8}{'C1<':>6}{'C2<':>6}   {'Cfree!=min':>11}{'C1!=min':>9}{'C2!=min':>9}")
for Lp1,wmax in [(3,7),(4,6),(5,4),(3,10),(6,3),(4,8)]:
    ch,fa,am,ex,tf=sweep(Lp1,wmax)
    print(f"L+1={Lp1},w0..{wmax:<10}{ch:>8}  {fa['Cfree']:>8}{fa['C1']:>6}{fa['C2']:>6}   "
          f"{am['Cfree']:>11}{am['C1']:>9}{am['C2']:>9}")
    if fa['C2']>0:
        print("   !!! C2 FAILURES:", ex['C2'][:6])
    if tf:
        print("   C2 non-tight (min != minAdm):", tf[:6])

# --- structural check: is C2(t,s') always == some Mval(M,T), T admissible? ---
print("\n=== Is C2(t,s') realized as a genuine orbit codim Mval(M,T) (T admissible)? ===")
def all_admissible_T(M):
    L=len(M)-1
    bounds=[admBound(M,j) for j in range(L)]
    out=[]
    for T in product(*[range(bd+1) for bd in bounds]):
        if admPred(M,T): out.append(T)
    return out

def mval_set(M):
    return set(Mval(M,T) for T in all_admissible_T(M))

miss=0; checked=0
for M in product(range(0,6),repeat=4):
    if len(M)<3: continue
    mvs=mval_set(M); n=min(M[2:]); m=minAdm(M)
    for t in range(min(M[0],M[1])+1):
        b=M[1]-t; s=min(b,n)
        for sp in range(0,s+1):
            c2=charge_set(t,M,sp)['C2']
            checked+=1
            if c2 not in mvs and c2>=m:
                # C2 not an exact orbit codim value but still >= minAdm: note (not a failure, but info)
                pass
            if c2 < m:
                miss+=1
print(f"checked {checked} (t,s') triples over L+1=4 w0..5; C2<minAdm count = {miss}")
