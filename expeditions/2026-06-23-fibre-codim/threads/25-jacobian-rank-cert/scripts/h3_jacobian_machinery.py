import sympy as sp
import random
random.seed(2024)

# ===== engine cValue (LR closed form, monotone d, r=0) =====
def qipA(d,l):
    N=len(d)-1
    s=sum(d[min(i,N)] for i in range(l+1))
    return s - l*d[min(l,N)]
def qipM(d):
    N=len(d)-1; best=0
    for l in range(0,N+1):
        if qipA(d,l)>=0: best=l
    return best
def cValue(d):
    N=len(d)-1; m=qipM(d); S=sum(d[i] for i in range(m+1))
    a=(2*S+m)//(2*m); delta=S-m*a; d0=d[0]
    val=(d0**2 - sum((d[i]-d0)**2 for i in range(1,m+1)) + m*(a-d0)**2 + 2*(a-d0)*delta + abs(delta))
    assert val%2==0; return val//2
def C_of(d,r):
    dr=[x-r for x in d]
    if min(dr)<0: return None
    return cValue(dr)

# ===== jacobian machinery =====
def build_factors(d):
    N=len(d)-1; return [sp.Matrix(d[i+1],d[i],lambda r,c,i=i: sp.Symbol(f'a{i}_{r}_{c}')) for i in range(N)]
def mult_expr(A):
    M=A[-1]
    for i in range(len(A)-2,-1,-1): M=M*A[i]
    return M
def all_vars(A):
    vs=[]
    for Ai in A: vs+=list(Ai)
    return vs
def card(d): return sum(d[i+1]*d[i] for i in range(len(d)-1))
def delta(d,r): return r*(d[0]+d[-1]-r)
_jc={}
def jac_and(d):
    k=tuple(d)
    if k in _jc: return _jc[k]
    A=build_factors(d); J=sp.Matrix([[sp.diff(o,v) for v in all_vars(A)] for o in list(mult_expr(A))])
    _jc[k]=(J,all_vars(A),A); return _jc[k]
def jac_rank_at(d,fv):
    J,vs,A=jac_and(d); subs={}
    for i,Ai in enumerate(A):
        for r in range(Ai.rows):
            for c in range(Ai.cols): subs[Ai[r,c]]=fv[i][r,c]
    return J.subs(subs).rank()
def prod_of(A):
    M=A[-1]
    for i in range(len(A)-2,-1,-1): M=M*A[i]
    return M

# ===== generic point =====
def rmat(rows,cols,lo=-4,hi=4): return sp.Matrix(rows,cols,lambda i,j: random.randint(lo,hi))
def rrank(rows,cols,rk):
    rk=min(rk,rows,cols)
    if rk==0: return sp.zeros(rows,cols)
    for _ in range(400):
        M=rmat(rows,rk)*rmat(rk,cols)
        if M.rank()==rk: return M
    raise RuntimeError("rrank")
def complement(M,n):
    if M.cols==n: return sp.Matrix(n,0,[])
    cur=M; out=[]
    for i in range(n):
        e=sp.zeros(n,1); e[i]=1; t=sp.Matrix.hstack(cur,e)
        if t.rank()==cur.cols+1: cur=t; out.append(e)
        if cur.cols==n: break
    return sp.Matrix.hstack(*out) if out else sp.Matrix(n,0,[])
def right_normal_gauge(P,r):
    n,m=P.shape; cols=P.columnspace(); C=sp.Matrix.hstack(*cols)
    Ccomp=complement(C,n); Linv=sp.Matrix.hstack(C,Ccomp) if Ccomp.cols else C; L=Linv.inv()
    D=(C.T*C).inv()*C.T*P; Drinv=D.T*(D*D.T).inv()
    Rcomp=complement(Drinv,m); R=sp.Matrix.hstack(Drinv,Rcomp) if Rcomp.cols else Drinv
    return L,R
def realize_profile(d,prof):
    N=len(d)-1; Pre=sp.eye(d[0]); A=[]
    for i in range(N):
        p_next=prof[i+1]; G=rrank(d[i+1],d[i],p_next); A.append(G); Pre=G*Pre
        if Pre.rank()!=p_next: return None
    P=Pre; r=prof[N]
    E=sp.Matrix(d[-1],d[0],lambda i,j:1 if(i==j and i<r) else 0)
    if r==0: return A if P==E else None
    L,R=right_normal_gauge(P,r)
    if L*P*R!=E: return None
    A=list(A); A[-1]=L*A[-1]; A[0]=A[0]*R
    return A
def enumerate_profiles(d,r):
    N=len(d)-1; profs=[]
    def rec(i,cur):
        if i==N:
            if r<=min(cur[-1],d[N]): profs.append(cur+[r])
            return
        for p in range(r, min(cur[-1],d[i])+1): rec(i+1,cur+[p])
    rec(1,[d[0]]); return profs
def generic_rank(d,r,trials=3):
    best=-1
    for prof in enumerate_profiles(d,r):
        for _ in range(trials):
            pt=realize_profile(d,prof)
            if pt is None: continue
            if prod_of(pt)!=sp.Matrix(d[-1],d[0],lambda i,j:1 if(i==j and i<r) else 0): continue
            best=max(best,jac_rank_at(d,pt))
    return best
