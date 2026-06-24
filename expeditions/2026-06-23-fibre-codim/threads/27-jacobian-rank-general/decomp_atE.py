# CORRECTED decomposition test: product pinned to EXACTLY E. Build A0 of rank rho0 with rowspace
# containing rows of E, solve A1 (product = E), across rho0 in [r, min]. At EACH such genuine
# fibre-over-E point, test: V_orbit = {M: BR block [r:,r:]=0} ⊆ image, and rank = δ + dim π_BR(image).
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros, Rational, symbols, linsolve
import random
random.seed(123)
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
        base=[]
        for j in range(r):
            v=[0]*d0; v[j]=1; base.append(v)
        for _ in range(rho0-r):
            base.append([random.randint(-3,3) for _ in range(d0)])
        Bm=Matrix(base)
        if Bm.rank()!=rho0: continue
        comb=randMatrix(d1,rho0,min=-3,max=3)
        A=comb*Bm
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
def test_N1(d,r):
    dN=d[2]; d0=d[0]; d1=d[1]; dl=r*(dN+d0-r)
    E=zeros(dN,d0)
    for j in range(r): E[j,j]=1
    BR=lambda out:[idx for idx,(rr,cc) in enumerate(out) if rr>=r and cc>=r]
    allok=True; vals=[]
    for rho0 in range(r,min(d1,d0)+1):
        A0=A0_rs(d1,d0,rho0,r)
        if A0 is None: continue
        A1=solveA1(A0,E)
        if A1 is None or chain([A0,A1])!=E: continue
        J,out=jacJ([A0,A1],d); rk=J.rank()
        cs=J.columnspace(); Bm=Matrix.hstack(*cs).T if cs else zeros(0,len(out))
        brc=BR(out); piBR=Bm[:,brc].rank() if Bm.rows>0 else 0
        cap=rk-piBR
        ok=(cap==dl) and (rk==dl+piBR)
        allok=allok and ok; vals.append(rk)
        print(f"   rho(A0)={rho0} rho(A1)={A1.rank()}: rk={rk} δ={dl} π_BR={piBR} cap={cap} {'OK' if ok else 'FAIL'}")
    print(f"d={d} r={r}: V_orbit⊆image (cap=δ) & rk=δ+π_BR at all E-points: {allok}; ranks={sorted(set(vals))}")
for d,r in [([2,2,2],1),([3,3,3],1),([3,2,3],1),([2,2,3],1),([3,3,3],2)]:
    test_N1(d,r)
