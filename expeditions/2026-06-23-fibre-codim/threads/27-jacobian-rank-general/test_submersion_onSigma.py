# Verify the Q3 closing logic at the genuine top-Σ̄^r/fibre points (E-pinned, section-built):
#   at a SMOOTH point A of a top component of Σ̄^r with rank(mult A)=r exactly:
#     (i)  rank(d g_A) = C   (g=π_BR∘mult, the Σ̄^r-defining map; codim Σ̄^r = C)
#     (ii) rank(d mult_A) = C+δ  (decomposition: V_orbit⊆image adds δ, transverse adds C)
#     (iii) the fibre F is smooth at A of codim C+δ in Rep, i.e. tangent T_A F = ker d mult_A has
#           dim card-(C+δ). [tangent = ker is the LANDED FibreJacobian identity; smoothness => dim=this]
# We CONFIRM (ii) at the top point and that card - rank = the Singular top-component dim.
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros, Rational, symbols, linsolve
import random
random.seed(777)
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
# Build the TOP component point: maximal endpoint freedom. For (3,3,3)r1 = both rank 2 (middle).
# Use the verified mid333 construction (rowspace span(e1,r2)).
def toppt(d,r):
    dN=d[-1]; d0=d[0]; d1=d[1]
    E=zeros(dN,d0)
    for j in range(r): E[j,j]=1
    e1=Matrix([[1]+[0]*(d0-1)])
    target_rho=min(d1,d0)  # middle rank as large as possible but product still r
    for _ in range(200):
        # A0 rank = target_rho with rowspace ⊇ e1..e_{r-1}, generic otherwise
        base=[Matrix([[1 if j==k else 0 for j in range(d0)]]) for k in range(r)]
        extra=target_rho-r
        rs=[Matrix([[random.randint(-3,3) for _ in range(d0)]]) for _ in range(extra)]
        rows=base+rs
        # pad to d1 rows as combos
        Bm=Matrix.vstack(*rows)
        if Bm.rank()!=target_rho: continue
        A0=randMatrix(d1,target_rho,min=-3,max=3)*Bm
        if A0.rank()!=target_rho: continue
        # solve A1
        syms=symbols(f'y0:{d1}'); A1r=[]; ok=True
        for rr in range(dN):
            x=Matrix([list(syms)]); eqs=(x*A0-E.row(rr))
            sol=linsolve([eqs[0,j] for j in range(d0)],list(syms))
            if not sol: ok=False;break
            s=list(sol)[0]; free=set()
            for c in s: free|=c.free_symbols
            sub={v:Rational(random.randint(-3,3)) for v in free}
            A1r.append([c.subs(sub) for c in s])
        if not ok: continue
        A1=Matrix(A1r)
        if chain([A0,A1])!=E: continue
        return [A0,A1],E
    return None,E
Cv={("2,2,2",1):(1,4),("3,3,3",1):(3,8),("3,2,3",1):(2,7),("3,3,3",2):(1,9)}
# top dims from Singular: (2,2,2)r1 ->4; (3,3,3)r1->10; (3,2,3)r1->? ; (3,3,3)r2->10
topdim={("2,2,2",1):4,("3,3,3",1):10,("3,3,3",2):10}
for d,r in [([2,2,2],1),([3,3,3],1),([3,3,3],2)]:
    facs,E=toppt(d,r)
    if facs is None: print(f"d={d} r={r}: no top pt"); continue
    dN=d[-1]; d0=d[0]; dl=r*(dN+d0-r); C,Cpd=Cv[(",".join(map(str,d)),r)]
    J,out=jacJ(facs,d); rk=J.rank(); card=sum(d[i+1]*d[i] for i in range(len(d)-1))
    print(f"d={d} r={r}: factor ranks={[f.rank() for f in facs]}, rank(d mult)={rk} "
          f"(C+δ={Cpd} {'OK' if rk==Cpd else 'MISS'}); card-rank={card-rk} "
          f"(Singular top dim={topdim.get((','.join(map(str,d)),r),'?')})")
