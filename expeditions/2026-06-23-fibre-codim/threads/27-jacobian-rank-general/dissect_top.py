import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros, Rational, symbols, linsolve
import random
random.seed(11)
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
# EXACT middle333 construction (gave rank 8): A0 rank2 with rowspace = span(e1, r2); solve A1.
def mid333(d,r):
    dN=d[-1]; d0=d[0]; d1=d[1]
    E=zeros(dN,d0)
    for j in range(r): E[j,j]=1
    e1=Matrix([[1]+[0]*(d0-1)])
    while True:
        r2=Matrix([[random.randint(-3,3) for _ in range(d0)]])
        c=random.randint(-3,3); dd=random.randint(-3,3); r3=c*e1+dd*r2
        rowsM=[e1,r2,r3][:d1] if d1>=3 else [e1,r2][:d1]
        A0=Matrix.vstack(*rowsM) if len(rowsM)==d1 else None
        if A0 is None or A0.rank()!=min(2,d1): continue
        # need rank exactly 2 (the middle); ensure d1>=2
        if A0.rank()!=2: continue
        # solve A1 A0 = E
        syms=symbols(f'y0:{d1}'); A1rows=[]; ok=True
        for rr in range(dN):
            x=Matrix([list(syms)]); eqs=(x*A0-E.row(rr))
            sol=linsolve([eqs[0,j] for j in range(d0)],list(syms))
            if not sol: ok=False; break
            s=list(sol)[0]; free=set()
            for comp in s: free|=comp.free_symbols
            subsd={v:Rational(random.randint(-3,3)) for v in free}
            A1rows.append([comp.subs(subsd) for comp in s])
        if not ok: continue
        A1=Matrix(A1rows)
        if chain([A0,A1])!=E: continue
        return [A0,A1],E
def dissect(d,r,facs):
    dN=d[-1]; d0=d[0]; dl=r*(dN+d0-r)
    J,out=jacJ(facs,d); rk=J.rank()
    cs=J.columnspace(); B=Matrix.hstack(*cs).T if cs else zeros(0,len(out))
    BR=[idx for idx,(rr,cc) in enumerate(out) if rr>=r and cc>=r]
    piBR=B[:,BR].rank() if B.rows>0 else 0
    cap=rk-piBR
    print(f"   ranks A0,A1={[f.rank() for f in facs]}; rank(dmult)={rk}; δ={dl}; rk-δ={rk-dl}; "
          f"π_BR={piBR}; image∩V_orbit={cap}")
    print(f"      V_orbit⊆image:{cap==dl}; extra-in-BR:{piBR==rk-dl}; "
          f"so image=V_orbit⊕(BR∩image), dim={cap}+{piBR}={cap+piBR}")
for dd,rr,Cgt in [([3,3,3],1,3),([3,2,3],1,2),([2,2,3],1,1)]:
    facs,E=mid333(dd,rr)
    print(f"d={dd} r={rr} (C={Cgt}, C+δ={Cgt+rr*(dd[-1]+dd[0]-rr)}):")
    dissect(dd,rr,facs)
