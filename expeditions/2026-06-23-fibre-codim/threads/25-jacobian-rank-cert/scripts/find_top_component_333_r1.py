import sympy as sp, random
random.seed(7)
def jr(d, factors):
    N=len(d)-1; syms=[]
    mats=[]
    for i in range(N):
        mats.append(sp.Matrix(d[i+1],d[i],lambda a,b,i=i: sp.Symbol(f's{i}_{a}_{b}')))
        syms+=[sp.Symbol(f's{i}_{a}_{b}') for a in range(d[i+1]) for b in range(d[i])]
    M=mats[-1]
    for i in range(N-2,-1,-1): M=M*mats[i]
    outs=[M[a,b] for a in range(d[-1]) for b in range(d[0])]
    J=sp.Matrix([[sp.diff(o,v) for v in syms] for o in outs])
    subs={}
    for i in range(N):
        for a in range(d[i+1]):
            for b in range(d[i]): subs[sp.Symbol(f's{i}_{a}_{b}')]=factors[i][a,b]
    return J.subs(subs).rank(), M.subs(subs)
# (3,3,3) r=1. Try the profile p=(3,2,1): A0 drops 3->2, A1 drops 2->1. i.e. running rank 3,2,1.
# A0 (3x3): rank so that running=2. A0 generic rank2. Prefix1 rank2.
# A1 (3x3): A1*Prefix1 rank 1. So A1 collapses the rank-2 prefix image to rank1, then gauge to E.
def rrank(rows,cols,rk):
    rk=min(rk,rows,cols)
    if rk==0: return sp.zeros(rows,cols)
    for _ in range(300):
        M=sp.Matrix(rows,rk,lambda i,j:random.randint(-3,3))*sp.Matrix(rk,cols,lambda i,j:random.randint(-3,3))
        if M.rank()==rk: return M
    raise RuntimeError
def complement(M,n):
    cur=M; out=[]
    for i in range(n):
        e=sp.zeros(n,1); e[i]=1; t=sp.Matrix.hstack(cur,e)
        if t.rank()==cur.cols+1: cur=t; out.append(e)
        if cur.cols==n: break
    return sp.Matrix.hstack(*out) if out else sp.Matrix(n,0,[])
def gauge(P,r):
    n,m=P.shape; cols=P.columnspace(); C=sp.Matrix.hstack(*cols)
    Cc=complement(C,n); Li=sp.Matrix.hstack(C,Cc) if Cc.cols else C; L=Li.inv()
    D=(C.T*C).inv()*C.T*P; Dr=D.T*(D*D.T).inv(); Rc=complement(Dr,m)
    R=sp.Matrix.hstack(Dr,Rc) if Rc.cols else Dr; return L,R

for prof in [(3,2,1),(3,1,1),(3,3,1)]:
    found=False
    for _ in range(20):
        # A0: running 3->prof[1]
        A0=rrank(3,3,prof[1])  # rank prof[1]
        Pre1=A0
        if Pre1.rank()!=prof[1]: continue
        # A1: A1 Pre1 rank prof[2]=1. Build A1 generic with rank(A1 Pre1)=1.
        # choose A1 = T * Pre1^+ + W*(I-proj). T rank1 (3 x prof[1]).
        Pb=sp.Matrix.hstack(*Pre1.columnspace())
        T=rrank(3,prof[1],prof[2]); Pbp=(Pb.T*Pb).inv()*Pb.T
        Proj=sp.eye(3)-Pb*Pbp; W=sp.Matrix(3,3,lambda i,j:random.randint(-3,3))
        A1=T*Pbp+W*Proj
        P=A1*A0
        if P.rank()!=1: continue
        L,R=gauge(P,1); E=sp.Matrix([[1,0,0],[0,0,0],[0,0,0]])
        if L*P*R!=E: continue
        A1g=L*A1; A0g=A0*R
        rk,prod=jr([3,3,3],[A0g,A1g])
        print(f"profile {prof}: rank={rk}, dim=card-rank={18-rk}  (C+delta=8, top dim=10)")
        found=True; break
    if not found: print(f"profile {prof}: no point found")
