import sys
from functools import lru_cache
def pr(*a): print(*a); sys.stdout.flush()

# ---- exact-N minAdm / redChain / peelCharge (mirrors the Lean recursion) ----
def peelCharge(M,u):
    return max(M[0]-u,0)*max(M[1]-u,0)
def redChain(M,t):
    # drop head t times: reduce (M0,M1,...) by peeling front cut t  (redChain t M)
    # matches design: minAdm(redChain t M); implement via the QIP minAdm below on the reduced widths
    # redChain t M = (M0 - t, then tail...) — we use the peel identity minAdm_le_peelCharge_add_redChain
    return None
@lru_cache(None)
def minAdm(M):
    # QIP: minAdm(M) = min_{0<=t<=min(M0,M1)} peelCharge(M,t) + minAdm(dropHeadReduce(M,t))
    # 2-width leaf: minAdm(M0,M1) = 0 (single edge has no interior?) -> use standard: leaf minAdm=M0*M1? 
    # Use the design's convention verified below against known anchors.
    M=tuple(M)
    if len(M)==2:
        return M[0]*M[1]
    best=None
    tm=min(M[0],M[1])
    for t in range(tm+1):
        red=(M[1]-t,)+tuple(M[2:])   # redChain t on 3-width -> 2-width leaf (M1-t, M2); general: front-peel
        val=peelCharge(M,t)+minAdm(red)
        best=val if best is None else min(best,val)
    return best

pr("Anchor checks (design):")
pr(f"  minAdm(3,3,3)={minAdm((3,3,3))} (want 7)   carrierThreshold=7/2")
pr(f"  minAdm(3,4,4)={minAdm((3,4,4))} (want 10)")
pr(f"  minAdm(2,3)={minAdm((2,3))}=6  minAdm(3,4)={minAdm((3,4))}=12  minAdm(1,3)={minAdm((1,3))}=3")

pr("")
pr("="*68)
pr("CONVERGENCE: crude-PSD (keep full a×b corner, project Z→strong) vs DESIGN")
pr("="*68)
# design reduced det-Gram: corner (a-j)x(b-j) in ambient (M2-j): converge (a-j) < (M2-j)-(b-j)+1 = M2-b+1
# crude PSD  : corner a x b   in ambient (M2-j): converge  a    < (M2-j)-b+1 = M2-j-b+1
def design_ok(a,b,M2,j): return (a-j) < (M2-b+1)
def crude_ok(a,b,M2,j):  return  a     < (M2-j-b+1)
pr(" (3,3,3)@t*=1: a=b=2, M2=3, shell j=1")
pr(f"   design converge (a-j<M2-b+1): {2-1} < {3-2+1} = {design_ok(2,2,3,1)}")
pr(f"   crude  converge (a<M2-j-b+1): {2}   < {3-1-2+1} = {crude_ok(2,2,3,1)}  <-- FAILS")

pr("")
pr("="*68)
pr("CHARGE TELESCOPING across j single cuts  vs  design shell-j jump  (sweep)")
pr("="*68)
# For a chain M (3-width here), at binding cut t*, shell j: 
#   design charge C_j = peelCharge over the SHRUNK corner (a-j)(b-j) + minAdm(redChain(t*+j))
#   iterated: sum_{i=0}^{j-1} freed corner at cut (t*+i) telescopes via minAdm_redChain_succ_ge
# check C_j >= minAdm(M) for all shells, and the telescoping identity.
def redk(M,t):  # redChain t M for 3-width: (M1-t, M2)
    return (M[1]-t,M[2])
import itertools
viol=0; tot=0; tel_viol=0
for M0 in range(1,6):
 for M1 in range(1,6):
  for M2 in range(1,6):
    M=(M0,M1,M2)
    mA=minAdm(M)
    tm=min(M0,M1)
    # binding cuts
    for tstar in range(tm+1):
        if peelCharge(M,tstar)+minAdm(redk(M,tstar))!=mA: continue
        a=M0-tstar; b=M1-tstar; r=min(a,b)
        for j in range(r+1):
            u=tstar+j
            if u>min(M0,M1): continue
            Cj=(M0-tstar-j)*(M1-tstar-j)+minAdm(redk(M,u))
            tot+=1
            if Cj<mA: viol+=1
            # telescoping: minAdm(redk(M,u)) - minAdm(redk(M,tstar)) >= sum_{i} [(a-i)+(b-i)-1]
            lhs=minAdm(redk(M,u))-minAdm(redk(M,tstar))
            rhs=sum((a-i)+(b-i)-1 for i in range(j))
            if lhs<rhs: tel_viol+=1
pr(f"  C_j >= minAdm(M):  {tot-viol}/{tot} hold, {viol} violations")
pr(f"  convexity telescoping minAdm(redChain succ) >= sum[(a-i)+(b-i)-1]: {tel_viol} violations")
