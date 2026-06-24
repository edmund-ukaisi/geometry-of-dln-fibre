#!/usr/bin/env python3
"""
Test the team-lead's sharpened crux: at a well-chosen rank-r point A (mult(A)=E),
    image(d mult_A) = V_orbit ⊕ V_C   in T(Mat) = Mat_{d_N×d_0},
where
  V_orbit = T_E Mat^{≤r} = {X E + E Y : X∈gl_{d_N}, Y∈gl_{d_0}} = {M : M_{[r:,r:]}=0}  (dim δ),
  V_C     = a C-dim complement coming from the Σ̄^r-transverse / "rank-can-increase" directions.

The image is a subspace of Mat (dim d_N·d_0). We compute exactly:
  - dim image(d mult_A) (should be C+δ at a generic top-component pt),
  - whether image ⊇ V_orbit (dim δ),  [verified before: yes, uniformly]
  - dim(image ∩ V_orbit)  (should be exactly δ, i.e. V_orbit ⊆ image),
  - the COMPLEMENT image/V_orbit, dim = (C+δ) − δ = C; identify it as the "bottom-right block can
    move to higher rank" directions, i.e. the projection of image onto Mat/V_orbit =
    Mat_{(d_N−r)×(d_0−r)} (the bottom-right block coords) is C-dimensional.

Concretely V_orbit = {M : bottom-right (d_N−r)×(d_0−r) block = 0}. So Mat/V_orbit ≅ the bottom-right
block, dim (d_N−r)(d_0−r). The complement V_C = (image projected to the bottom-right block). Claim:
  dim image = δ + dim(π_{BR}(image)),  where π_BR: Mat → bottom-right block,
and dim(π_BR(image)) = C  ⟺ the direct sum holds with the C-part = bottom-right-block image.
Note (d_N−r)(d_0−r) = "C_single" (single-matrix codim) ≥ C always; equality iff C = (d_N−r)(d_0−r).
The thread-14 DEAD-route note: C_single ≠ C in general (they differ at r=0). So is V_C the WHOLE
bottom-right block (dim C_single) or a C-dim subspace of it? TEST IT.
"""
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros, Rational, symbols, linsolve
import random
random.seed(31)

def chain(f):
    M=f[-1]
    for k in range(len(f)-2,-1,-1): M=M*f[k]
    return M
def jac(facs,d):
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
    return J, out   # J rows indexed by out=(r,c) entries of Mat

def col_space_basis(J):
    # image of d mult = column space of J (rows = Mat entries, cols = Rep coords).
    return J  # we'll use J.columnspace via rank on submatrices

def cCodim_lookup(d,r):
    Cval={("2,2,2",0):3,("2,2,2",1):1,("2,2,2",2):0,("2,2,3",1):1,("3,2,3",1):2,
          ("3,3,3",1):3,("3,3,3",2):1,("1,2,1",0):1,("1,2,1",1):0,("2,2,2,2",1):1,
          ("2,3,2",1):1,("4,4,4",2):3,("3,4,3",1):4}
    return Cval.get((",".join(map(str,d)),r))

def build_witness(d,r):
    """A well-chosen rank-r fibre point: A0=A1=...= block-structured so mult=E exactly and the
    point is a GENERIC point of the top component. Use the 'middle' construction: each inner factor
    = identity-ish, endpoints carry E. Simplest faithful generic top-comp pt for N=1:
    pick A0 rank rho0, A1 rank rho1 with the MIDDLE rank = r and BOTH endpoint ranks maximal
    subject to product=E (the top component). We reuse the random middle-branch sampler."""
    N=len(d)-1
    E=zeros(d[N],d[0])
    for j in range(r): E[j,j]=1
    # For the TOP component, the 'inner rank' is r and endpoint factors as large as possible.
    # Generic construction: choose the chain to factor through a rank-r middle uniformly.
    # Build: pick generic full-rank maps that compose to E with maximal endpoint freedom.
    # We'll just sample random fibre points and KEEP one whose rank(d mult) is the MAX (top comp).
    best=None
    for _ in range(60):
        facs=[]
        ok=True
        # random factors with product E: hard to hit exactly by random; instead use the
        # parametrized top-comp construction for N=1, and a generic-gauge for N>=2.
        if N==1:
            # solve A1 A0 = E with A0 rank-(rho0) generic whose rowspace contains rows of E.
            # take A0 generic rank min(d1,d0) (=full if square) with rowspace ⊇ rowspace(E),
            # then A1 determined-up-to-freedom; pick generic.
            rho0=min(d[1],d[0])
            # build A0 rank rho0 with rowspace containing e_0..e_{r-1} (rows of E that are nonzero)
            A0=_rand_rowspace_contains(d[1],d[0],rho0,r)
            A1=_solve_A1(A0,E,d)
            if A1 is None: continue
            facs=[A0,A1]
        else:
            # N>=2: build a chain that composes to E; gauge generically.
            facs=_chain_to_E(d,r,E)
            if facs is None: continue
        if chain(facs)!=E: continue
        J,out=jac(facs,d); rk=J.rank()
        if best is None or rk>best[0]:
            best=(rk,facs,J,out)
    return best,E

def _rand_rowspace_contains(rows,cols,rk,r,lo=-3,hi=3):
    # rows×cols matrix of rank rk whose row space contains e_0..e_{r-1} (first r std basis rows of k^cols)
    import sympy as sp
    while True:
        # take first r rows = e_0..e_{r-1}; remaining rk-r rows random; pad to 'rows' rows as combos
        base=[]
        for j in range(r):
            v=[0]*cols; v[j]=1; base.append(v)
        for _ in range(rk-r):
            base.append([random.randint(lo,hi) for _ in range(cols)])
        B=Matrix(base)  # rk × cols
        if B.rank()!=rk: continue
        # build 'rows' rows as random combos of base
        comb=randMatrix(rows,rk,min=lo,max=hi)
        A=comb*B
        if A.rank()==rk: return A

def _solve_A1(A0,E,d):
    # solve A1 A0 = E for A1 (rows independent); pick generic free params
    a,b,c=None,None,None
    dN=d[1]; d0=d[0]
    cols=d[1]  # A1 is dN x d1? careful: A1: d1->d2=d_N. shapes: A0: d0->d1, A1: d1->d2.
    # A1 A0 : d0 -> d2.  A1 is (d2 x d1). For each row r of A1 (length d1): row_r(A1) A0 = E[r,:]
    d1=A0.rows  # A0 is d1 x d0
    d2=E.rows
    rows=[]
    syms=symbols(f'y0:{d1}')
    for rr in range(d2):
        x=Matrix([list(syms)])
        eqs=(x*A0 - E.row(rr))
        sol=linsolve([eqs[0,j] for j in range(d0)], list(syms))
        if not sol: return None
        s=list(sol)[0]
        free=set()
        for comp in s: free|=comp.free_symbols
        subsd={v:Rational(random.randint(-3,3)) for v in free}
        rows.append([comp.subs(subsd) for comp in s])
    return Matrix(rows)

def _chain_to_E(d,r,E):
    # N>=2: simplest -- A0 = generic rank>=r, then middle factors identity-padded, last absorbs.
    # Just build A_i = block diag pieces so product = E. Use: A_i = I-ish carrying rank r.
    N=len(d)-1
    facs=[]
    # Build factors so the composite = E: put E's action at vertex 0->1, identity-on-rank-r after.
    # A_0: d1 x d0 with top-left r×r = I_r, else 0 (rank r). A_i (1<=i<=N-2): d_{i+1} x d_i top-left
    # I_r else 0. A_{N-1}: d_N x d_{N-1} top-left I_r else 0. Composite top-left = I_r => product=E.
    for i in range(N):
        Ai=zeros(d[i+1],d[i])
        for j in range(r): Ai[j,j]=1
        facs.append(Ai)
    # gauge generically by random units at INNER vertices only (keep endpoints to preserve E? no:
    # inner gauge preserves the product exactly). Apply random inner units.
    U=[None]*(N+1)
    for v in range(1,N): U[v]=_rand_inv(d[v])
    U[0]=eye(d[0]); U[N]=eye(d[N])
    for i in range(N):
        facs[i]=U[i+1]*facs[i]*U[i].inv()
    return facs

def _rand_inv(n,lo=-3,hi=3):
    while True:
        M=randMatrix(n,n,min=lo,max=hi)
        if M.det()!=0: return M

def analyze(d,r):
    N=len(d)-1; dN=d[N]; d0=d[0]; card=sum(d[i+1]*d[i] for i in range(N)); dl=r*(dN+d0-r)
    C=cCodim_lookup(d,r)
    best,E=build_witness(d,r)
    if best is None:
        print(f"d={d} r={r}: NO witness built"); return
    rk,facs,J,out=best
    # V_orbit = {M : bottom-right (dN-r)x(d0-r) block = 0}; its complement coords = BR block entries.
    # index of out=(r,c) that are in BR block: r>=r and c>=r ... careful naming: r is the rank param.
    BR_rows=[idx for idx,(rr,cc) in enumerate(out) if rr>=r and cc>=r]
    # image = columnspace(J) in coordinate space indexed by out. Project to BR coords: take submatrix
    # of J with rows = BR_rows, its rank = dim π_BR(image).
    J_BR = J[BR_rows,:]
    dim_piBR = J_BR.rank()
    # dim(image ∩ V_orbit): image has dim rk; π_BR(image) dim dim_piBR; kernel of π_BR|_image =
    # image ∩ V_orbit, dim = rk - dim_piBR.
    dim_img_cap_Vorbit = rk - dim_piBR
    Vorbit_dim = card  # placeholder
    Vorbit_dim = dN*d0 - (dN-r)*(d0-r)  # = δ
    BRblock = (dN-r)*(d0-r)  # = C_single
    print(f"d={d} r={r}: card={card}, δ={dl}, C={C}, C+δ={None if C is None else C+dl}, dN·d0={dN*d0}")
    print(f"   witness rank(d mult)={rk}  (top comp value)")
    print(f"   δ (=dim V_orbit) = {dl}; bottom-right block dim (C_single)=(dN-r)(d0-r)={BRblock}")
    print(f"   dim π_BR(image) = {dim_piBR}   (claim: = C = {C})")
    print(f"   dim(image ∩ V_orbit) = rk - dim_piBR = {dim_img_cap_Vorbit}   (claim: = δ = {dl})")
    ok1 = (C is not None and dim_piBR==C)
    ok2 = (dim_img_cap_Vorbit==dl)
    ok3 = (rk == (C+dl if C is not None else -1))
    print(f"   => image = V_orbit ⊕ V_C with dim V_C = C : "
          f"{'YES' if (ok1 and ok2 and ok3) else 'partial/NO'}  "
          f"(piBR=C:{ok1}, cap=δ:{ok2}, rk=C+δ:{ok3})")

for d,r in [([2,2,2],0),([2,2,2],1),([2,2,2],2),([2,2,3],1),([3,2,3],1),
            ([3,3,3],1),([3,3,3],2),([1,2,1],0),([1,2,1],1),([2,2,2,2],1),([2,3,2],1)]:
    try:
        analyze(d,r)
    except Exception as e:
        print(f"d={d} r={r}: ERROR {e}")
