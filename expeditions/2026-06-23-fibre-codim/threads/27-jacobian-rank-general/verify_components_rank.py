#!/usr/bin/env python3
"""
The CORRECT per-component verification: at a GENERIC SMOOTH point of each genuine
irreducible component F_alpha of the fibre, rank(d mult_A) = card - dim F_alpha.
We do NOT use factor-rank strata (which mislead). Instead we use Singular's primary
decomposition to get the components' dims, and verify:
  - the top component has codim = C+delta;
  - rank(d mult) at a generic point of EACH component F_alpha equals card - dim F_alpha,
    hence >= C+delta (since dim F_alpha <= dim(top) = card-C-delta).
We pick a generic point of a component by taking a random point on the component's
parametrization. Simplest faithful route: for the TOP component pick a generic point
with factor ranks giving the maximal stratum; for LOWER components, pick a point on the
lower stratum that is GENERIC IN ITS COMPONENT. But identifying components without Singular
is exactly what misled us. So here we cross-check ONLY the robust claims:
  (1) the TOP value of rank(d mult) over ALL fibre points = C+delta (= card - dim fibre);
  (2) rank(d mult) is LOWER-SEMICONTINUOUS, so its MIN over the fibre is the value at the
      most singular point (E-image / zero-ish), and its generic value on the top component
      is the MAX. The hard-direction bound needs: at a generic SMOOTH point of every
      component, rank >= C+delta. Singular gives dim of every component; card - dim_component
      = rank at a generic SMOOTH point of that component (generic smoothness). Since
      dim_component <= dim(top component) = card-C-delta, we get rank >= C+delta automatically.
So the per-component bound is a TAUTOLOGY given:
  (a) generic smoothness (rank at generic smooth pt of F_alpha = card - dim F_alpha), and
  (b) dim F_alpha <= dim(top) = card - C - delta  -- i.e. the TOP component is the biggest,
      with dim exactly card - C - delta.
The ONLY nontrivial inputs are (a) [standard char 0] and the identity dim(top) = card-C-delta.

This script just confirms numerically, via the MAX Jacobian rank over many random fibre
points (achieved on the top component, generic smooth) = C+delta, for the cases where
Singular gave us the component dims.
"""
import sympy as sp
from sympy import randMatrix, eye, zeros
import random
random.seed(99)

def chain(facs):
    M=facs[-1]
    for k in range(len(facs)-2,-1,-1): M=M*facs[k]
    return M
def suffix(facs,i):
    N=len(facs)
    if i==N-1: return eye(facs[N-1].rows)
    M=facs[N-1]
    for k in range(N-2,i,-1): M=M*facs[k]
    return M
def prefix(facs,i):
    if i==0: return eye(facs[0].cols)
    M=facs[i-1]
    for k in range(i-2,-1,-1): M=M*facs[k]
    return M
def jac(facs,d):
    N=len(facs); dN=d[N]; d0=d[0]
    out=[(r,c) for r in range(dN) for c in range(d0)]
    cols=[(i,s,t) for i in range(N) for s in range(d[i+1]) for t in range(d[i])]
    J=zeros(len(out),len(cols))
    S=[suffix(facs,i) for i in range(N)]; P=[prefix(facs,i) for i in range(N)]
    for ri,(rr,cc) in enumerate(out):
        for ci,(i,s,t) in enumerate(cols):
            J[ri,ci]=S[i][rr,s]*P[i][t,cc]
    return J
def rand_rk(rows,cols,rk,lo=-5,hi=5):
    while True:
        L=randMatrix(rows,rk,min=lo,max=hi)
        if L.rank()==rk: break
    while True:
        Rm=randMatrix(rk,cols,min=lo,max=hi)
        if Rm.rank()==rk: break
    return L*Rm

# For each (d,r), build many random fibre-stratum points across ALL profiles giving
# composite rank r, and record (composite rank, rank d mult). The MAX rank over all such
# points = value on the top component = C+delta. Also record the rank at the generic point
# of each profile stratum (= card - dim of that stratum's GENERIC SMOOTH point, valid only
# if the stratum is a component or open in one; we DON'T claim that). We only certify:
#   max over fibre = C+delta, AND every profile's generic rank >= ... let's just print.
from itertools import product as iproduct
def profiles(d,r):
    N=len(d)-1
    return list(iproduct(*[range(r,min(d[i+1],d[i])+1) for i in range(N)]))

cases=[([2,2,2],1,4),([3,3,3],1,8),([3,2,3],1,7),([2,2,3],1,5),([2,2,2,2],1,4)]
for d,r,Cpd in cases:
    N=len(d)-1; cd=sum(d[i+1]*d[i] for i in range(N))
    maxrk=-1; per={}
    for prof in profiles(d,r):
        ranks=[]
        for _ in range(6):
            facs=[rand_rk(d[i+1],d[i],prof[i]) for i in range(N)]
            if chain(facs).rank()!=r: continue
            ranks.append(jac(list(facs),d).rank())
        if ranks:
            per[prof]=max(ranks)
            maxrk=max(maxrk,max(ranks))
    print(f"d={d} r={r}: card={cd}, engine C+delta={Cpd}, MAX rank(dmult) over fibre={maxrk}  "
          f"{'== C+delta OK' if maxrk==Cpd else '** != C+delta **'}")
    for prof,rk in sorted(per.items()):
        print(f"     profile {prof}: generic rank(dmult)={rk}  (card-rank={cd-rk})")
