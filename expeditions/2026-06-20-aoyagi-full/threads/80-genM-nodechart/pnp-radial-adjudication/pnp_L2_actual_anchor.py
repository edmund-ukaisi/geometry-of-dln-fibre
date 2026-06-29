import sympy as sp, random
random.seed(4)
# ACTUAL genBlkFlatLiveR1: anchor = pivotEIndicator at E-block (0,0) of pivot boundary p (=1 at L=2);
#   the freed E-slot (0,0)'s coordinate is rerouted to the live leaf (leaf fully free, t1*M2 free coords).
# So active = {structPivot} ∪ {E-block of bd1 EXCEPT (0,0)} ∪ {ALL leaf coords}.
#   #active = 1 + (r1*c1 - 1) + t1*M2 = r1*c1 + t1*M2 = minAdm. SAME count, anchor in E not leaf.
M0,M1,M2,t1=2,3,2,1; r1=M0-t1; c1=M1-t1
u=sp.Symbol('u',real=True)
def SM(name,r,c): return sp.Matrix(r,c, lambda i,j: sp.Symbol(f'{name}_{i}_{j}',real=True)) if r*c>0 else sp.zeros(r,c)
K=SM('K',t1,t1); X=SM('X',r1,t1); N=SM('N',t1,c1); W=SM('W',c1,M2)
# E-block: (0,0) is the FIXED anchor =1 (pivotEIndicator); rest free.
E=SM('E',r1,c1); 
if r1>0 and c1>0: E[0,0]=sp.Integer(1)
lf=SM('lf',t1,M2)   # leaf FULLY free (the rerouted budget)
Bmat1=sp.Matrix.vstack(K,X*K); qN1=sp.Matrix.hstack(sp.eye(t1),N)
R1=sp.zeros(M0,M1)
for i in range(r1):
    for j in range(c1): R1[t1+i,t1+j]=E[i,j]
C2=u*lf; C1=Bmat1*qN1+u*R1; A0=C1; A1=sp.Matrix.vstack(C2-N*W,W)
F=[sp.expand(A[i,j]) for A in (A0,A1) for i in range(A.rows) for j in range(A.cols)]
allv=[u]+sorted({s for e in F for s in e.free_symbols if s!=u},key=str)
print(f"ACTUAL (E-anchor, free leaf): #free coords={len(allv)} flatDim={len(F)} square={len(allv)==len(F)}")
J=sp.Matrix(F).jacobian(sp.Matrix(allv))
sub={v:sp.Rational(random.randint(1,9),random.randint(1,5)) for v in allv if v!=u}
P=sp.Poly(sp.expand(J.subs(sub).det()),u)
minAdm=r1*c1+t1*M2
print(f"  det u-poly = {P.as_expr()}  u-degree={P.degree()} minAdm-1={minAdm-1} match={P.degree()==minAdm-1} single-monomial={len(P.terms())==1}")
# active = {u} ∪ {E free (excl (0,0))} ∪ {leaf all free}
Efree=[E[i,j] for i in range(r1) for j in range(c1) if E[i,j]!=sp.Integer(1)]
leaffree=[lf[i,j] for i in range(t1) for j in range(M2)]
active=[u]+Efree+leaffree
print(f"  active = u + E-free{[str(e) for e in Efree]} + leaf-free{[str(l) for l in leaffree]}  card={len(active)} (minAdm={minAdm}) match={len(active)==minAdm}")
