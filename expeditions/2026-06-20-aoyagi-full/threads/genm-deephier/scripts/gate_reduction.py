"""
Gate reduction (arity 4..7): the honest deep-factor codim is minAdm((u,)+deep) [reduced-rank-regression
codim of the (front u)x(deep chain) product; the minAdm recursion IS the multi-scale-across-layers
resolution -> Aoyagi rlct=codim/2].  Gate:  minAdm((u,)+deep) >= minAdm(M) - a*b = 2T1q.
This is the t=u term of  minAdm(M)=min_t (M0-t)(M1-t)+minAdm((t,)+deep) <= (M0-u)(M1-u)+minAdm((u,)+deep).
Verify 0 violations across arities; also report how often it is TIGHT (u a minAdm-minimizer).
"""
import itertools
from functools import lru_cache

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    m0,m1=M[0],M[1]; rest=M[2:]
    return min((m0-t)*(m1-t)+minAdm((t,)+rest) for t in range(0,min(m0,m1)+1))

def binding_cut(M):
    m0,m1=M[0],M[1]; rest=M[2:]
    best=None;targ=None
    for t in range(0,min(m0,m1)+1):
        val=(m0-t)*(m1-t)+minAdm((t,)+rest)
        if best is None or val<best: best=val;targ=t
    return targ,min(m0-targ,m1-targ)

def minimizers(M):
    m0,m1=M[0],M[1]; rest=M[2:]
    best=minAdm(M); mins=[]
    for t in range(0,min(m0,m1)+1):
        if (m0-t)*(m1-t)+minAdm((t,)+rest)==best: mins.append(t)
    return mins

for arity,W in [(4,9),(5,7),(6,6),(7,5)]:
    nwidths=arity
    ncut=0; viol=0; tight=0; minslack=None; rankgen_fail=0
    for M in itertools.product(range(1,W+1),repeat=nwidths):
        deep=M[2:]
        tstar,r=binding_cut(M)
        mins=minimizers(M)
        for j in range(1,r):
            u=tstar+j; a=M[0]-u;b=M[1]-u
            if a<1 or b<1: continue
            rho=min(deep)
            if not (a+b<=rho-1): rankgen_fail+=1; continue   # rankgen scope
            ncut+=1
            floor=minAdm((u,)+deep); target=minAdm(M)-a*b
            slack=floor-target
            if minslack is None or slack<minslack: minslack=slack
            if slack<0: viol+=1
            if slack==0: tight+=1
    print(f"arity {arity} (widths 1..{W}): cuts(in rankgen scope)={ncut}  gate VIOLATIONS(minAdm((u,)+deep)<2T1q)={viol}  "
          f"min slack={minslack}  TIGHT(=2T1q)={tight}")
