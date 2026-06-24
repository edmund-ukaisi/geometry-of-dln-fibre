#!/usr/bin/env python3
"""
Find the TOP component's generic Jacobian rank directly, the honest way:
parametrize the top component of mult^{-1}(E) and evaluate rank(d mult) at a generic
rational point of it (a SMOOTH point), with exact arithmetic.

Structure of the top component (LR / type-A): the fibre over E=diag(I_r,0) decomposes by
how the rank-r "flows through" the chain. The TOP (biggest) component corresponds to the
GENERIC factorization: write the section. For (3,3,3) r=1: E has rank 1. A generic point of
the top stratum: choose A0, A1 of generic ranks so that the product is E but with the MOST
free parameters. From Singular: top dim = 10. Let's parametrize the SET of (A0,A1) with
A1 A0 = E by the explicit "graph" of the rank-r chart and sample a generic rational point.

We use the Schur/section parametrization: split k^3 = k^1 ⊕ k^2 at source and target.
E = [[1,0,0],[0,0,0],[0,0,0]]. A point of the fibre: A1 A0 = E.
Generic construction of a fibre point with A0 of rank rho0, A1 of rank rho1:
  Choose A0 arbitrary (rank rho0). For A1 A0 = E we need A1 to send col-space appropriately.
This is a linear condition on A1 given A0 (and vice versa). To get a GENERIC point of the
fibre (not of a factor-rank stratum), we solve: fix A0 generic of FULL rank 3? No - if A0
full rank then A1 = E A0^{-1}, rank(A1)=rank(E)=1, giving a specific component. Let's just
enumerate by which factor is "full":
  Branch P0: A0 invertible (rank 3), A1 = E A0^{-1} (rank 1). Free params: A0 in GL_3 = 9 dim
     (open), A1 determined. dim of this branch = 9. (closure = a component, dim 9.)
  Branch P1: A1 invertible (rank 3), A0 = A1^{-1} E (rank 1). dim 9.
  These are the dim-9 components! The dim-10 TOP component must be the one where NEITHER
  endpoint is invertible -- the generic "rank drops at the middle" locus.
Let's just sample the fibre by solving A1 A0 = E with A0, A1 BOTH rank 1 or 2 generically and
measure rank(d mult), and separately sample branch P0/P1, to locate where rank = 8 occurs.
"""
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros, Rational
import random
random.seed(2024)

def chain(facs):
    M=facs[-1]
    for k in range(len(facs)-2,-1,-1): M=M*facs[k]
    return M
def jac222like(facs,d):
    N=len(facs); dN=d[N]; d0=d[0]
    def suffix(i):
        if i==N-1: return eye(facs[N-1].rows)
        M=facs[N-1]
        for k in range(N-2,i,-1): M=M*facs[k]
        return M
    def prefix(i):
        if i==0: return eye(facs[0].cols)
        M=facs[i-1]
        for k in range(i-2,-1,-1): M=M*facs[k]
        return M
    out=[(r,c) for r in range(dN) for c in range(d0)]
    cols=[(i,s,t) for i in range(N) for s in range(d[i+1]) for t in range(d[i])]
    J=zeros(len(out),len(cols))
    S=[suffix(i) for i in range(N)]; P=[prefix(i) for i in range(N)]
    for ri,(rr,cc) in enumerate(out):
        for ci,(i,s,t) in enumerate(cols):
            J[ri,ci]=S[i][rr,s]*P[i][t,cc]
    return J

d=[3,3,3]
E=Matrix([[1,0,0],[0,0,0],[0,0,0]])

def rand_inv(n,lo=-4,hi=4):
    while True:
        M=randMatrix(n,n,min=lo,max=hi)
        if M.det()!=0: return M

print("Branch P0: A0 in GL_3 random, A1 = E A0^{-1} (so A1A0=E).")
for _ in range(3):
    A0=rand_inv(3); A1=E*A0.inv()
    assert chain([A0,A1])==E
    J=jac222like([A0,A1],d)
    print(f"   rank A0={A0.rank()}, rank A1={A1.rank()}, rank(d mult)={J.rank()}, card-rank={9*2-J.rank()}")

print("Branch P1: A1 in GL_3 random, A0 = A1^{-1} E.")
for _ in range(3):
    A1=rand_inv(3); A0=A1.inv()*E
    assert chain([A0,A1])==E
    J=jac222like([A0,A1],d)
    print(f"   rank A0={A0.rank()}, rank A1={A1.rank()}, rank(d mult)={J.rank()}, card-rank={18-J.rank()}")

print("\nGeneric MIDDLE branch: A0 rank2, A1 rank2, product rank1 = E.")
# Need A1 A0 = E with both rank 2. Solve: pick A0 rank2 with the right column space, A1 rank2.
# Construct: A0 = U0 [[I2],[0]]-ish... Let's just solve linear system: fix A0 (rank 2) generic,
# find A1 with A1 A0 = E. A1 A0 = E is 9 linear eqns in 9 entries of A1. Solvable iff E's rows
# are in row-space(A0)?? Actually A1 A0 = E => each row of E is (row of A1) * A0, i.e. E's rows in
# the row space of A0. row space of A0 (rank 2) is a 2-dim subspace of k^3. E's nonzero row is
# e1=[1,0,0]; need e1 in rowspace(A0). Generic rank-2 A0 has 2-dim rowspace; e1 in it is a
# codim-1 condition. So pick A0 rank2 whose rowspace contains e1.
def rand_rk(rows,cols,rk,lo=-4,hi=4):
    while True:
        L=randMatrix(rows,rk,min=lo,max=hi)
        if L.rank()==rk: break
        R=randMatrix(rk,cols,min=lo,max=hi)
    while True:
        R=randMatrix(rk,cols,min=lo,max=hi)
        if R.rank()==rk: break
    return L*R

cnt=0; tries=0
while cnt<3 and tries<2000:
    tries+=1
    A0=rand_rk(3,3,2)
    # solve A1 A0 = E for A1 (9x9 linear). Vectorize: for each row r of A1 (3 unknowns), row_r(A1) A0 = row_r(E)
    sol_rows=[]
    ok=True
    for rr in range(3):
        # x A0 = E[rr,:]  => A0^T x^T = E[rr,:]^T
        rhs=E.row(rr).T
        try:
            xsol = A0.T.solve(rhs)  # particular; but A0^T may be singular (rank2) -> use gauss
            sol_rows.append(xsol.T)
        except Exception:
            ok=False; break
    if not ok: continue
    # A0^T rank 2 => solvable only if rhs in colspace(A0^T)=rowspace... use lstsq-free exact:
    # Better: use linsolve over the augmented system per row, allow free params -> pick random.
    # Redo with explicit nullspace handling:
    A1rows=[]
    feasible=True
    AT=A0.T
    ns=AT.nullspace()  # right nullspace of A0^T = left nullspace of A0
    for rr in range(3):
        rhs=E.row(rr).T
        # solve AT x = rhs
        aug=AT.row_join(rhs)
        # check consistency
        if AT.rank()!=aug.rank():
            feasible=False; break
        part=AT.gauss_jordan_solve(rhs)[0] if True else None
        # gauss_jordan_solve returns (particular, params); substitute random for free params
        psol,params=AT.gauss_jordan_solve(rhs)
        if params.free_symbols:
            subsd={s:Rational(random.randint(-3,3)) for s in params.free_symbols}
            psol=psol.subs(subsd)
        A1rows.append(psol.T)
    if not feasible: continue
    A1=Matrix.vstack(*A1rows)
    if chain([A0,A1])!=E: continue
    J=jac222like([A0,A1],d)
    print(f"   rank A0={A0.rank()}, rank A1={A1.rank()}, rank(d mult)={J.rank()}, card-rank={18-J.rank()}")
    cnt+=1
print("Done.")
