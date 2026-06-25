#!/usr/bin/env python3
"""
Diagnose the (3,3,3) r=1 discrepancy.
  thread-25 cert: rank(d mult) at generic TOP-component point = 8, C+delta=8 (so C=3).
  my fibre-component experiment: min over strata rank(d mult) = 5 (profile [1,1]), so C=0.

These conflict. Resolve by computing:
  (A) dim of the fibre over E (rank-1) = card - rank(d mult at generic fibre point)
      directly via the largest stratum.
  (B) codim Sigma^1 = card - dim Sigma^1  (Sigma^1 = {A : rank(A1 A0) <= 1}).
  (C) cross-check (2,2,2) r=1 where both agree (rank 4 = C+delta = 1+3).

Key question: is the cert's "8" the rank at a generic point of a TOP-dim component
of the FIBRE, or did it compute rank at a non-generic / wrong point?
For (3,3,3) r=1: profile [1,1] gives composite rank 1 generically and dim S=13, rank(dmult)=5.
If that is a genuine fibre component (the BIGGEST), then C+delta = 5, C=0 -- meaning
Sigma^1 for (3,3,3) has codim 0?? That cannot be (Sigma^1 is a proper subvariety).
So either profile [1,1] does NOT generically have composite rank 1, OR dim S_[1,1] != 13.
Investigate carefully with many random samples + exact ranks.
"""
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros
import random
random.seed(7)

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
    for ri,(r,c) in enumerate(out):
        for ci,(i,s,t) in enumerate(cols):
            J[ri,ci]=S[i][r,s]*P[i][t,c]
    return J
def rand_rk(rows,cols,rk,lo=-5,hi=5):
    while True:
        L=randMatrix(rows,rk,min=lo,max=hi)
        if L.rank()==rk: break
    while True:
        R=randMatrix(rk,cols,min=lo,max=hi)
        if R.rank()==rk: break
    return L*R

d=[3,3,3]; r=1
print("=== (3,3,3), profile [1,1]: many samples, composite rank + jacobian rank ===")
crank_counts={}
jrank_counts={}
for trial in range(8):
    A0=rand_rk(3,3,1); A1=rand_rk(3,3,1)
    prod=A1*A0
    cr=prod.rank()
    crank_counts[cr]=crank_counts.get(cr,0)+1
    J=jac([A0,A1],d); jr=J.rank()
    jrank_counts.setdefault(cr,[]).append(jr)
    print(f"  trial {trial}: composite rank={cr}, rank(dmult)={jr}")
print("  composite-rank distribution:", crank_counts)
print("  jacobian-rank by composite rank:", jrank_counts)

print("\n=== Cross-check (2,2,2) profile [1,1], r=1 ===")
d2=[2,2,2]
for trial in range(4):
    A0=rand_rk(2,2,1); A1=rand_rk(2,2,1)
    prod=A1*A0; cr=prod.rank()
    J=jac([A0,A1],d2); jr=J.rank()
    print(f"  trial {trial}: composite rank={cr}, rank(dmult)={jr}")

print("\n=== Estimate dim Sigma^1 for (3,3,3) by the rank-<=1 image-variety dimension ===")
# Sigma^1 = image-closure of {(A0,A1): rank(A1 A0)<=1}. The product B=A1 A0 ranges over rank<=1
# 3x3 matrices (dim of rank<=1 3x3 = 5). The fibre over a generic rank-1 B: dim = card - dim(image).
# We estimate dim Sigma^1 = max stratum dim of {rank(A1A0)<=1}. The biggest stratum has
# A0,A1 full rank... no: if A0,A1 both rank 3 then product rank 3 > 1. So to have product rank<=1
# you constrain. The generic way to get product rank exactly 1 with the FEWEST constraints:
# Let's directly find, over random samples with prescribed factor ranks, which (rho0,rho1) admit
# composite rank 1, and the dimension of that stratum = card - rank(d mult at its generic pt) but
# only if that point is a SMOOTH point of Sigma^1 (which requires it be generic in a component of
# Sigma^1, the rank<=1 locus, NOT the fibre).
# Simpler: dim Sigma^1 = card - codim Sigma^1. We compute codim Sigma^1 as the codim of the
# rank-<=1 product locus directly via a generic-fibre count over the rank-1 base:
#   mult: Rep -> Mat, restricted to Sigma^1 surjects onto {rank<=1} (dim 5). Over a generic rank-1
#   B, fibre dim = (the biggest stratum's dim). dim Sigma^1 = 5 + (fibre dim).  (IF dominant + the
#   generic fibre is the biggest stratum.)
print("  (see component experiment: top fibre dim was 13 for profile [1,1])")
print("  => if dim(fibre over rank-1 B) = 13 then dim Sigma^1 = 5 + 13 = 18 = card => codim 0?!")
print("  That is ABSURD (Sigma^1 proper). So profile [1,1] is NOT generic-composite-rank-1, OR")
print("  the rank(dmult)=5 point is NOT a smooth point of the fibre (dim != card-rank there).")
