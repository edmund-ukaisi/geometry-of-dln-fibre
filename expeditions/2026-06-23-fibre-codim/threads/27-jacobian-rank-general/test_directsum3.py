#!/usr/bin/env python3
"""
Use the VERIFIED top-component constructions (confirm222 / middle333: rank=C+δ) and dissect the
image of d mult_A inside Mat. Goal: locate the +C directions and test the lead's V_orbit ⊕ V_C.

For N=1, the components are the 'endpoint-rank' branches. The TOP-rank value C+δ is achieved by:
  - (2,2,2) r=1: A0 invertible, A1=E A0^{-1} -> rank 4 = C+δ. (BOTH branches give 4, both TOP.)
  - (3,3,3) r=1: the MIDDLE branch (both rank 2) -> rank 8 = C+δ. (Endpoint-invertible branches
    give 9 > 8, lower components.)
So 'top component' is dimension-vector-dependent. We pick, per case, the construction that achieves
rank = C+δ (the MIN over components = the genuine top/biggest component).
"""
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros, Rational, symbols, linsolve
import random
random.seed(99)

def chain(f):
    M=f[-1]
    for k in range(len(f)-2,-1,-1): M=M*f[k]
    return M
def jacJ(facs,d):
    N=len(facs);dN=d[N];d0=d[0]
    def suf(i):
        if i==N-1: return eye(facs[N-1].rows)
        M=facs[N-1]
        for k in range(N-2,i,-1):M=M*facs[k]
        return M
    def pre(i):
        if i==0: return eye(facs[0].cols)
        M=facs[i-1]
        for k in range(i-2,-1,-1):M=M*facs[k]
        return M
    out=[(rr,cc) for rr in range(dN) for cc in range(d0)]
    cols=[(i,s,t) for i in range(N) for s in range(d[i+1]) for t in range(d[i])]
    J=zeros(len(out),len(cols)); S=[suf(i) for i in range(N)]; P=[pre(i) for i in range(N)]
    for ri,(rr,cc) in enumerate(out):
        for ci,(i,s,t) in enumerate(cols): J[ri,ci]=S[i][rr,s]*P[i][t,cc]
    return J,out
def rand_inv(n,lo=-4,hi=4):
    while True:
        M=randMatrix(n,n,min=lo,max=hi)
        if M.det()!=0: return M
Cval={("2,2,2",1):1,("3,3,3",1):3,("3,2,3",1):2,("2,2,3",1):1,("3,3,3",2):1,("4,4,4",2):3}

def mid_branch_333like(d,r):
    """both 3x3 factors rank 2 (middle), product = E rank 1: the (3,3,3)r1 top component.
    General: both endpoint factors rank = (r + something). We use: A0 rank2 rowspace ⊇ e1, solve A1."""
    dN=d[2] if len(d)==3 else d[-1]; d0=d[0]
    E=zeros(d[-1],d[0])
    for j in range(r): E[j,j]=1
    d1=d[1]
    # A0: d1 x d0 rank min(d1,d0)-?; we want the MIDDLE: choose A0 of rank that maximizes freedom.
    # empirically for (3,3,3)r1 rank-2 both. Let's sample A0 over ranks and keep MIN-rank-dmult point.
    best=None
    for rho0 in range(r, min(d1,d0)+1):
        for _ in range(40):
            A0=_A0(d1,d0,rho0,r)
            if A0 is None: continue
            A1=_A1(A0,E)
            if A1 is None: continue
            if chain([A0,A1])!=E: continue
            J,out=jacJ([A0,A1],d); rk=J.rank()
            if best is None or rk<best[0]:  # MIN over branches = top/biggest component
                best=(rk,[A0,A1],J,out)
    return best,E
def _A0(d1,d0,rho0,r):
    for _ in range(30):
        base=[]
        for j in range(r):
            v=[0]*d0; v[j]=1; base.append(v)
        for _ in range(rho0-r):
            base.append([random.randint(-3,3) for _ in range(d0)])
        B=Matrix(base)
        if B.rank()!=rho0: continue
        comb=randMatrix(d1,rho0,min=-3,max=3)
        A=comb*B
        if A.rank()==rho0: return A
    return None
def _A1(A0,E):
    d1=A0.rows; d0=A0.cols; d2=E.rows
    syms=symbols(f'y0:{d1}'); rows=[]
    for rr in range(d2):
        x=Matrix([list(syms)]); eqs=(x*A0-E.row(rr))
        sol=linsolve([eqs[0,j] for j in range(d0)],list(syms))
        if not sol: return None
        s=list(sol)[0]; free=set()
        for comp in s: free|=comp.free_symbols
        subsd={v:Rational(random.randint(-3,3)) for v in free}
        rows.append([comp.subs(subsd) for comp in s])
    return Matrix(rows)

def dissect(d,r,facs,J,out,rk,C):
    dN=d[-1]; d0=d[0]; dl=r*(dN+d0-r)
    cs=J.columnspace()
    B=Matrix.hstack(*cs).T if cs else zeros(0,len(out))
    BRcoords=[idx for idx,(rr,cc) in enumerate(out) if rr>=r and cc>=r]
    dim_piBR = B[:,BRcoords].rank() if B.rows>0 else 0
    dim_cap = rk - dim_piBR
    print(f"   rank={rk} (C+δ={C+dl}{' MATCH' if rk==C+dl else ' MISS'}); "
          f"π_BR(image)={dim_piBR} (BRdim={(dN-r)*(d0-r)}); image∩V_orbit={dim_cap} (δ={dl}); "
          f"rk-δ={rk-dl} (C={C})")
    # Is V_orbit ⊆ image? need image ⊇ all M with BR-block 0. dim V_orbit=δ. image∩V_orbit dim=dim_cap.
    print(f"      V_orbit⊆image: {dim_cap==dl}; extra (rk-δ={rk-dl}) live in BR: {dim_piBR==rk-dl}")

print("=== (2,2,2) r=1: A0 invertible branch (rank 4 = C+δ) ===")
d=[2,2,2]; r=1; E=zeros(2,2); E[0,0]=1
A0=rand_inv(2); A1=E*A0.inv()
J,out=jacJ([A0,A1],d);
dissect(d,r,[A0,A1],J,out,J.rank(),1)

print("=== (3,3,3) r=1: MIN-rank branch (top component, rank 8 = C+δ) ===")
for dd,rr in [([3,3,3],1),([3,2,3],1),([2,2,3],1),([3,3,3],2)]:
    best,E=mid_branch_333like(dd,rr)
    if best:
        rk,facs,J,out=best
        print(f"d={dd} r={rr}:")
        dissect(dd,rr,facs,J,out,rk,Cval[(",".join(map(str,dd)),rr)])
