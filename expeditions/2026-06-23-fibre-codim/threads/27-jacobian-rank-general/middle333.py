#!/usr/bin/env python3
"""Generic point of the MIDDLE component (both factors rank 2, product = E rank 1) for (3,3,3) r=1.
Construct it cleanly. We want A1 A0 = E, rank A0 = rank A1 = 2.
Build via the section: pick a generic 2-dim subspace W (= im A0 = the "middle" space), with the
rank-1 image of E factoring through W. Concretely:
  A0 : k^3 -> k^3 of rank 2, image = W (random 2-dim), so A0 = B0 with col space W.
  A1 : k^3 -> k^3 of rank 2 with A1|_W giving the right rank-1 composite = E.
We solve A1 A0 = E directly as a linear system in A1's 9 entries (3 rows x 3 cols), with A0 fixed
rank-2 whose ROW space contains e1=[1,0,0] (necessary for solvability since rows of E = rows of
A1 times A0 lie in rowspace(A0)). Then pick A1 GENERIC in the solution affine space with the extra
free params (so A1 is generic rank 2), and read rank(d mult)."""
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros, Rational, symbols, linsolve
import random
random.seed(11)

def chain(facs):
    M=facs[-1]
    for k in range(len(facs)-2,-1,-1): M=M*facs[k]
    return M
def jac(facs,d):
    N=len(facs); dN=d[N]; d0=d[0]
    def suf(i):
        if i==N-1: return eye(facs[N-1].rows)
        M=facs[N-1]
        for k in range(N-2,i,-1): M=M*facs[k]
        return M
    def pre(i):
        if i==0: return eye(facs[0].cols)
        M=facs[i-1]
        for k in range(i-2,-1,-1): M=M*facs[k]
        return M
    out=[(r,c) for r in range(dN) for c in range(d0)]
    cols=[(i,s,t) for i in range(N) for s in range(d[i+1]) for t in range(d[i])]
    J=zeros(len(out),len(cols))
    S=[suf(i) for i in range(N)]; P=[pre(i) for i in range(N)]
    for ri,(rr,cc) in enumerate(out):
        for ci,(i,s,t) in enumerate(cols):
            J[ri,ci]=S[i][rr,s]*P[i][t,cc]
    return J

d=[3,3,3]
E=Matrix([[1,0,0],[0,0,0],[0,0,0]])

def rand_A0_rank2_rowspace_contains_e1():
    # rowspace must contain e1=[1,0,0]. Build A0 with rows: r1=e1, r2=random, r3 = lin comb of r1,r2
    e1=Matrix([[1,0,0]])
    while True:
        r2=Matrix([[random.randint(-3,3) for _ in range(3)]])
        c=random.randint(-3,3); dd=random.randint(-3,3)
        r3=c*e1+dd*r2
        A0=Matrix.vstack(e1,r2,r3)
        if A0.rank()==2:
            return A0

found=0; tries=0
while found<5 and tries<500:
    tries+=1
    A0=rand_A0_rank2_rowspace_contains_e1()
    # Solve A1 A0 = E: for each row rr, x_rr A0 = E[rr,:]. x_rr is 1x3 unknown.
    a,b,c=symbols('a b c')
    A1rows=[]
    ok=True
    for rr in range(3):
        x=Matrix([[a,b,c]])
        eqs=(x*A0 - E.row(rr))
        sol=linsolve([eqs[0,0],eqs[0,1],eqs[0,2]],[a,b,c])
        if not sol: ok=False; break
        solset=list(sol)[0]
        # substitute random for free symbols
        free=set()
        for comp in solset: free|=comp.free_symbols
        subsd={s:Rational(random.randint(-3,3)) for s in free}
        row=[comp.subs(subsd) for comp in solset]
        A1rows.append(row)
    if not ok: continue
    A1=Matrix(A1rows)
    if chain([A0,A1])!=E: continue
    J=jac([A0,A1],d)
    print(f"A0 rank={A0.rank()}, A1 rank={A1.rank()}, rank(d mult)={J.rank()}, dim(=card-rank)={18-J.rank()}")
    found+=1
print(f"(found {found} middle-branch points in {tries} tries)")
