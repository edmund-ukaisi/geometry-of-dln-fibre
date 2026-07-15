import sympy as sp
def analyze(name, base0, base1, base2):
    a=sp.symbols('a0:4'); b=sp.symbols('b0:4'); c=sp.symbols('c0:4')
    A=sp.Matrix(2,2,a); B=sp.Matrix(2,2,b); C=sp.Matrix(2,2,c)
    L0=sp.Matrix(base0)+A; L1=sp.Matrix(base1)+B; L2=sp.Matrix(base2)+C
    Z=sp.expand(L2*L1*L0)
    assert sp.Matrix(base2)*sp.Matrix(base1)*sp.Matrix(base0)==sp.zeros(2), name+" not a fiber pt"
    loss=sp.expand(sum(z**2 for z in Z))
    allv=list(a)+list(b)+list(c)
    poly=sp.Poly(loss,*allv)
    md=min(sum(m) for m in poly.monoms())
    lead=sum(cf*sp.prod([v**k for v,k in zip(allv,m)]) for m,cf in poly.terms() if sum(m)==md)
    # Hessian rank of the quadratic part (if md==2)
    print(f"--- {name}: min-deg={md}")
    if md==2:
        H=sp.hessian(lead,allv); r=H.rank()
        print(f"    quadratic leading form, Hess rank = {r} (Morse-Bott codim); rlct(quad)={sp.Rational(r,2)}")
        # residual: is there higher-order in ker(Hess)? Check next-degree terms restricted to ker directions
        ns=H.nullspace()
        print(f"    #kernel directions (potential higher-order) = {len(ns)}")
        if len(ns)>0:
            # collect degree-3,4 terms to see residual structure (in original vars)
            higher={d:[] for d in (3,4)}
            for m,cf in poly.terms():
                if sum(m) in (3,4):
                    supp={allv[i]:m[i] for i in range(len(m)) if m[i]>0}
                    higher[sum(m)].append((cf,supp))
            for d in (3,4):
                if higher[d]: print(f"    deg-{d} terms (sample):", higher[d][:6])
    else:
        print(f"    leading form (deg {md}):", sp.simplify(lead))
        lp=sp.Poly(lead,*allv)
        for m,cf in lp.terms():
            supp={allv[i]:m[i] for i in range(len(m)) if m[i]>0}
            print("      ",cf,supp)

# deep aligned point: L0=diag(1,0),L1=diag(1,0),L2=diag(0,1)
analyze("aligned diag (1,0)/(1,0)/(0,1)", [[1,0],[0,0]],[[1,0],[0,0]],[[0,0],[0,1]])
# chain nilpotent alignment
analyze("nilpotent chain", [[0,1],[0,0]],[[0,1],[0,0]],[[0,1],[0,0]])
# L1L0=0 with both rank1 aligned, L2 generic-ish invertible
analyze("L1L0=0 aligned, L2=I", [[1,0],[0,0]],[[0,0],[0,1]],[[1,0],[0,1]])
