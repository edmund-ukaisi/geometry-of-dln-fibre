# Hypothesis: dim π_BR(image(d mult_A)) = rank(d(π_BR∘mult)_A) = codim_{Rep}(Σ̄^r component through A)
#   at a generic point of that Σ̄^r component (since π_BR∘mult cuts Σ̄^r in the E-chart).
# i.e. the '+C' count = the codim of the Σ̄^r-stratum through A, which is ≥ C (= min codim Σ̄^r comp),
# with equality iff A is on a TOP Σ̄^r component. We test:  dim π_BR(image) = card − dim(Σ̄^r-stratum
# through A)  at the E-points, by comparing to the factor-rank-stratum codim in Σ̄^r.
# Actually simplest robust check: is dim π_BR(image) ALWAYS ≥ C (the lead's needed bound)? And does
# the MIN of dim π_BR(image) over genuine top E-points = C? We already see ranks for (3,3,3)r1:
# π_BR ∈ {2,3,4}; C=3; min is 2 < C at the rank-7 (singular) point. So π_BR ≥ C is FALSE at singular
# points (π_BR=2 < 3). So '+C' bound also fails pointwise at singular points -- same lesson.
# => dim π_BR(image) ≥ C holds at GENERIC component points, NOT uniformly. Confirm + locate.
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros, Rational, symbols, linsolve
import random
random.seed(55)
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
def A0_rs(d1,d0,rho0,r):
    for _ in range(40):
        base=[[0]*d0 for _ in range(0)]
        base=[]
        for j in range(r):
            v=[0]*d0; v[j]=1; base.append(v)
        for _ in range(rho0-r): base.append([random.randint(-3,3) for _ in range(d0)])
        Bm=Matrix(base)
        if Bm.rank()!=rho0: continue
        A=randMatrix(d1,rho0,min=-3,max=3)*Bm
        if A.rank()==rho0: return A
    return None
def solveA1(A0,E):
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
Cv={("2,2,2",1):1,("3,3,3",1):3,("3,2,3",1):2,("2,2,3",1):1,("3,3,3",2):1}
for d,r in [([2,2,2],1),([3,3,3],1),([3,2,3],1),([2,2,3],1),([3,3,3],2)]:
    dN=d[2]; d0=d[0]; d1=d[1]; dl=r*(dN+d0-r); C=Cv[(",".join(map(str,d)),r)]
    E=zeros(dN,d0)
    for j in range(r): E[j,j]=1
    BRc=lambda out:[i for i,(rr,cc) in enumerate(out) if rr>=r and cc>=r]
    piBRs=[]
    for rho0 in range(r,min(d1,d0)+1):
        A0=A0_rs(d1,d0,rho0,r)
        if A0 is None: continue
        A1=solveA1(A0,E)
        if A1 is None or chain([A0,A1])!=E: continue
        J,out=jacJ([A0,A1],d); cs=J.columnspace()
        Bm=Matrix.hstack(*cs).T if cs else zeros(0,len(out))
        piBR=Bm[:,BRc(out)].rank() if Bm.rows>0 else 0
        piBRs.append((rho0,A1.rank(),piBR))
    print(f"d={d} r={r}: C={C}; (ρ0,ρ1,π_BR): {piBRs}; min π_BR={min(p for _,_,p in piBRs)} "
          f"(≥C? {min(p for _,_,p in piBRs)>=C}); MAX over the BIGGEST-comp... C=min over TOP comps")
