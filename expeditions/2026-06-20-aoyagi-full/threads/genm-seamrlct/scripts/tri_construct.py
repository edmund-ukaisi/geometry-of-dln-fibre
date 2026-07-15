import sympy as sp, itertools
E=lambda i,j:sp.Matrix([[1 if (r,c)==(i,j) else 0 for c in range(2)] for r in range(2)])
def analyze(name,bases):
    Zb=bases[3]*bases[2]*bases[1]*bases[0]
    if sp.expand(Zb)!=sp.zeros(2,2):
        print(name,"NOT fiber pt"); return
    syms=[];pert=[]
    for i in range(4):
        s=sp.symbols(f'q{i}_0:4'); syms+=list(s); pert.append(sp.Matrix(2,2,s))
    Ls=[bases[i]+pert[i] for i in range(4)]
    Z=sp.expand(Ls[3]*Ls[2]*Ls[1]*Ls[0]); loss=sp.expand(sum(z**2 for z in Z))
    poly=sp.Poly(loss,*syms); md=min(sum(m) for m in poly.monoms())
    lo=lambda i:int(str(syms[i])[1])
    supp=set(tuple(sorted(set(lo(i) for i in range(len(m)) if m[i]>0))) for m,cf in poly.terms() if sum(m)==md)
    # also the FULL variable-level incidence (which individual vars couple) for a finer triangle check
    edges=set(s for s in supp if len(s)==2)
    tri=None
    for a,b,c in itertools.combinations(range(4),3):
        if (a,b) in edges and (b,c) in edges and (a,c) in edges: tri=(a,b,c)
    H=sp.hessian(loss,syms).subs({v:0 for v in syms}); r=sp.Matrix(H).rank()
    print(f"{name}: md={md}, Hess-rank={r}, layer-supports={sorted(supp)}, TRIANGLE={tri}")
    return supp

# generic invertible A3
A3=sp.Matrix([[2,1],[1,3]])
# candidate: A2=E00,A1=E11 (A2A1=0), A0=E00
analyze("A3 gen, A2=E00,A1=E11,A0=E00", [E(0,0),E(1,1),E(0,0),A3])
# variant to try to open all three edges: A2=E00,A1=E11,A0=E11
analyze("A3 gen, A2=E00,A1=E11,A0=E11", [E(1,1),E(1,1),E(0,0),A3])
# fully rank-1 cyclic-ish: A0=E10,A1=E01,A2=E10 (check A2A1A0 etc)
analyze("A0=E10,A1=E01,A2=E10", [E(1,0),E(0,1),E(1,0),A3])
# A2A1=0 and A1A0=0 both (double removal)
analyze("A2=E00,A1=E11,A0=E10 (A1A0=0?)", [E(1,0),E(1,1),E(0,0),A3])
