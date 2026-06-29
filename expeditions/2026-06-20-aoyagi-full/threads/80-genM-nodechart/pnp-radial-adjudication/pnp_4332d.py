import sympy as sp, random
random.seed(11)
u=sp.Symbol('u',real=True)
# symbolic free vars
def SM(name,r,c):
    return sp.Matrix(r,c, lambda i,j: sp.Symbol(f'{name}_{i}_{j}',real=True))
K1=SM('K1',3,3); X1=SM('X1',1,3)
K2=SM('K2',2,2); X2=SM('X2',1,2); N2=SM('N2',2,1); E2=sp.Symbol('E2',real=True); W2=SM('W2',1,2)
lf=SM('lf',2,2); lf[1,1]=sp.Integer(1)   # leaf anchor
B1=sp.Matrix.vstack(K1, X1*K1); B2=sp.Matrix.vstack(K2, X2*K2)
qN1=sp.eye(3); qN2=sp.Matrix.hstack(sp.eye(2), N2)
R1=sp.zeros(4,3); R2=sp.zeros(3,3); R2[2,2]=E2
C3=u*lf; C2=B2*qN2 + u*R2; C1=B1*qN1 + u*R1
A0=C1; A1=C2; A2=sp.Matrix.vstack(C3 - N2*W2, W2)
F=[]
for A in (A0,A1,A2):
    for i in range(A.rows):
        for j in range(A.cols):
            F.append(sp.expand(A[i,j]))
# all free vars (order: u first)
allv=[u]
for M in (K1,X1,K2,X2,N2,W2,lf):
    for e in M:
        if e.free_symbols and list(e.free_symbols)[0] not in allv and e!=sp.Integer(1):
            s=list(e.free_symbols)[0]
            if s not in allv: allv.append(s)
allv.append(E2)
allv=list(dict.fromkeys(allv))
print("num vars:", len(allv), " num outputs:", len(F), " (expect 27, 27)")
J=sp.Matrix(F).jacobian(sp.Matrix(allv))
# substitute non-u vars with random exact rationals -> Jacobian over QQ[u]
sub={v: sp.Rational(random.randint(-9,9), random.randint(1,6)) for v in allv if v!=u}
Ju=J.subs(sub)
det=sp.factor(sp.expand(Ju.det()))
print("det Dphi (non-u vars at random exact rationals) =", det)
P=sp.Poly(sp.expand(Ju.det()), u)
print("u-degree of det =", P.degree(), " (expect minAdm-1 = 4)")
# the det should be c * u^4 (a monomial in u). check it's a monomial:
terms=P.all_terms()
nonzero=[(deg,co) for (deg,),co in P.terms()]
print("u-monomial terms (deg,coeff):", nonzero, " (expect single term at deg 4)")
