#!/usr/bin/env python3
"""
CORRECTED: at the GENUINE top-component point (rank = C+δ), locate where the image of d mult_A
sits inside Mat_{d_N×d_0}, and test the lead's decomposition image = V_orbit ⊕ V_C.

Top-component witness: for N=1, the top component is the 'middle' branch (both factors of maximal
rank subject to product=E). We build it by the verified middle333 method and generalize. For N>=2
we GAUGE the canonical chain by random units at ALL vertices (not just inner) -- but endpoint gauge
moves E, so we gauge inner only and ALSO take generic full-rank factor blocks. Crucially we must
land rank(d mult)=C+δ (verify against the engine C). We retry until we hit the max rank.

Then: V_orbit = T_E Mat^{≤r} = {M : bottom-right (dN-r)×(d0-r) block = 0} (dim δ).
We compute the FULL image subspace (column space of J in Mat-coords) and:
  - dim image (=C+δ?),
  - dim(image ∩ V_orbit),
  - dim(image + V_orbit) = dim image + δ - dim(image∩V_orbit),
  - whether V_orbit ⊆ image (image∩V_orbit = δ), and dim image - δ = C (the genuine +C count),
  - WHERE the +C directions live: project image onto Mat/V_orbit (= bottom-right block); if that
    projection has dim < C, the +C does NOT live purely in the BR block -- so the lead's
    'orbit-dirs ⊕ Σ̄^r-transverse(BR) dirs' geometry is WRONG and the real V_C overlaps V_orbit's
    span direction. Report the truth.
"""
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros, Rational, symbols, linsolve
import random
random.seed(202606)

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

Cval={("2,2,2",0):3,("2,2,2",1):1,("2,2,2",2):0,("2,2,3",1):1,("3,2,3",1):2,
      ("3,3,3",1):3,("3,3,3",2):1,("1,2,1",0):1,("1,2,1",1):0,("2,2,2,2",1):1,
      ("2,3,2",1):1}

def rand_inv(n,lo=-3,hi=3):
    while True:
        M=randMatrix(n,n,min=lo,max=hi)
        if M.det()!=0: return M

def top_witness_N1(d,r,maxrank):
    """For N=1: top component. We search random fibre points and keep the MAX-rank one."""
    dN=d[1]; d0=d[0]
    E=zeros(dN,d0)
    for j in range(r): E[j,j]=1
    best=None
    for _ in range(200):
        # random A0 of rank rho0 in [r, min(dN,d0)] whose rowspace ⊇ rows of E; then solve A1.
        rho0=random.randint(r,min(dN,d0))
        A0=_A0_rowspace(d0,d0 if False else d0, dN, rho0, r, dom=d0, codom=d[1])
        # A0 shape: d1 x d0  (d1 = d[1]); rows of E live in k^{d0}
        if A0 is None: continue
        A1=_solveA1(A0,E)
        if A1 is None: continue
        facs=[A0,A1]
        if chain(facs)!=E: continue
        J,out=jacJ(facs,d); rk=J.rank()
        if best is None or rk>best[0]:
            best=(rk,facs,J,out)
        if best[0]==maxrank: break
    return best,E

def _A0_rowspace(d0,_unused,dN,rho0,r,dom,codom):
    # A0 : codom × dom  (= d1 × d0), rank rho0, rowspace (subspace of k^dom=k^d0) contains e_0..e_{r-1}
    d1=codom; d0=dom
    for _ in range(40):
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

def _solveA1(A0,E):
    d1=A0.rows; d0=A0.cols; d2=E.rows
    syms=symbols(f'y0:{d1}')
    rows=[]
    for rr in range(d2):
        x=Matrix([list(syms)])
        eqs=(x*A0 - E.row(rr))
        sol=linsolve([eqs[0,j] for j in range(d0)], list(syms))
        if not sol: return None
        s=list(sol)[0]; free=set()
        for comp in s: free|=comp.free_symbols
        subsd={v:Rational(random.randint(-3,3)) for v in free}
        rows.append([comp.subs(subsd) for comp in s])
    return Matrix(rows)

def top_witness_chain(d,r,maxrank):
    """N>=2: gauge the canonical rank-r chain by random units at INNER vertices, and also try
    higher-rank factor blocks at random to reach the top component. Keep MAX-rank point."""
    N=len(d)-1; dN=d[N]; d0=d[0]
    E=zeros(dN,d0)
    for j in range(r): E[j,j]=1
    best=None
    for _ in range(120):
        # random middle factorization: pick factors with the largest ranks that still compose to E.
        # Build A_i = L_i R_i full-rank rho_i; tune rho to hit composite r and max d mult rank.
        facs=[]
        # canonical: top-left I_r else 0, but bump some factor ranks up via random padding that
        # the next factor kills. Simplest robust: inner-gauge the canonical chain AND randomize.
        for i in range(N):
            Ai=zeros(d[i+1],d[i])
            for j in range(r): Ai[j,j]=1
            facs.append(Ai)
        U=[eye(d[0])]+[rand_inv(d[v]) for v in range(1,N)]+[eye(d[N])]
        for i in range(N):
            facs[i]=U[i+1]*facs[i]*U[i].inv()
        if chain(facs)!=E: continue
        J,out=jacJ(facs,d); rk=J.rank()
        if best is None or rk>best[0]: best=(rk,facs,J,out)
        if best[0]==maxrank: break
    return best,E

def image_basis_in_Mat(J,out,dN,d0):
    """Columns of J span image ⊆ Mat (Mat-coords = out). Return a Matrix whose ROWS are a basis of
    the image, each row a vector in Mat-coords (length dN*d0)."""
    cs=J.columnspace()  # list of column vectors (length len(out))
    if not cs: return zeros(0,len(out))
    return Matrix.hstack(*cs).T  # rows = basis vectors

def analyze(d,r):
    N=len(d)-1; dN=d[N]; d0=d[0]; dl=r*(dN+d0-r); C=Cval.get((",".join(map(str,d)),r))
    target=None if C is None else C+dl
    if N==1: best,E=top_witness_N1(d,r,target)
    else: best,E=top_witness_chain(d,r,target)
    if best is None: print(f"d={d} r={r}: no witness"); return
    rk,facs,J,out=best
    B=image_basis_in_Mat(J,out,dN,d0)   # rows = image basis, in Mat-coords
    # V_orbit = {M: bottom-right block zero}. Its complement coords = BR entries.
    BRcoords=[idx for idx,(rr,cc) in enumerate(out) if rr>=r and cc>=r]
    # projection of image onto BR coords:
    if B.rows>0:
        B_BR = B[:, BRcoords]
        dim_piBR = B_BR.rank()
    else:
        dim_piBR=0
    dim_cap = rk - dim_piBR  # image ∩ V_orbit
    print(f"d={d} r={r}: δ={dl} C={C} C+δ={target} dN·d0={dN*d0} | witness rank={rk}"
          f"{' [TOP]' if rk==target else ' [NOT TOP -- builder missed]'}")
    print(f"      dim π_BR(image)={dim_piBR} (BR block dim={(dN-r)*(d0-r)});  "
          f"dim(image∩V_orbit)={dim_cap} (δ={dl});  +C count = rk-δ = {rk-dl}")
    if rk==target:
        # where do the extra rk-δ directions live? rk-δ should be C. If dim_piBR < C, the extra
        # directions are NOT purely in BR block.
        print(f"      => extra dirs beyond V_orbit: {rk-dl} (claim C={C}); of these, "
              f"{dim_piBR} project nonzero to BR block, {rk-dl-dim_piBR} lie in V_orbit-span overlap")

for d,r in [([2,2,2],1),([3,3,3],1),([3,2,3],1),([2,2,3],1),([3,3,3],2),([2,2,2,2],1),([2,3,2],1)]:
    try: analyze(d,r)
    except Exception as e:
        import traceback; print(f"d={d} r={r} ERR {e}")
