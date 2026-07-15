import sympy as sp
# Can a 3-layer DLN germ realize the TRIANGLE (ab)^2+(ac)^2+(bc)^2 as leading transverse form?
# Codex Q4: expansion (A+a)(B+b)(C+c), ABC=0 => pairwise terms abC, aBc, Abc (coeffs C,B,A).
# For a triangle need A,B,C != 0 (edges) BUT linear terms aBC, A b C, ABc must vanish on the
# relevant subspace. STRUCTURAL constraint: middle-linear term is the sandwich  b -> A b C, which
# vanishes for all b iff A=0 or C=0.  With rank-deficient A,C there is a KERNEL subspace of b.
# Try rank-1 cyclic alignment in 3x3 to open that room.
def leading(base, dims=(3,3,3,3)):
    A=sp.Matrix(base[0]); B=sp.Matrix(base[1]); C=sp.Matrix(base[2])
    na=A.shape; nb=B.shape; nc=C.shape
    a=sp.symbols(f'a0:{na[0]*na[1]}'); b=sp.symbols(f'b0:{nb[0]*nb[1]}'); c=sp.symbols(f'c0:{nc[0]*nc[1]}')
    dA=sp.Matrix(na[0],na[1],a); dB=sp.Matrix(nb[0],nb[1],b); dC=sp.Matrix(nc[0],nc[1],c)
    assert (A*B*C)==sp.zeros(na[0],nc[1]), "not fiber pt"
    Z=sp.expand((A+dA)*(B+dB)*(C+dC))
    loss=sp.expand(sum(z**2 for z in Z))
    allv=list(a)+list(b)+list(c)
    poly=sp.Poly(loss,*allv); md=min(sum(m) for m in poly.monoms())
    lead=sum(cf*sp.prod([v**k for v,k in zip(allv,m)]) for m,cf in poly.terms() if sum(m)==md)
    H=sp.hessian(lead,allv) if md==2 else None
    return md, sp.simplify(lead), (H.rank() if H is not None else None), allv

# cyclic rank-1: A=e1 e2^T, B=e2 e3^T, C=e3 e1^T  (3x3). ABC = e1 e2^T e2 e3^T e3 e1^T = e1 (e2.e2)(e3.e3) e1^T
# = e1 e1^T != 0. Need ABC=0. Shift: A=e1 e2^T, B=e2 e3^T, C=e3 e2^T? then BC=e2 e3^T e3 e2^T=e2 e2^T, ABC=e1 e2^T e2 e2^T=e1e2^T !=0.
# Try nilpotent cyclic on 3 dims with a gap so ABC=0:
E=lambda i,j: sp.Matrix(3,3,lambda r,c:1 if (r,c)==(i,j) else 0)
for name,base in {
  "A=E01,B=E12,C=E20 (3-cycle)": (E(0,1),E(1,2),E(2,0)),
  "A=E01,B=E12,C=E21":            (E(0,1),E(1,2),E(2,1)),
  "A=E01+E10 sym cyc":            (E(0,1),E(1,2),E(2,0)+E(0,2)),
}.items():
    A,B,C=base
    prod=sp.expand(A*B*C)
    if prod!=sp.zeros(3,3):
        print(f"{name}: ABC != 0 (not a fiber pt), skip"); continue
    md,lead,hr,allv=leading(base)
    print(f"{name}: min-deg={md}, Hess-rank={hr}")
    print("   leading form:", lead)
