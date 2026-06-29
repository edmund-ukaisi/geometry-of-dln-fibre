import sympy as sp, random
random.seed(3)
# (3,3,3) Fix B. Text=[3,3,1], Wext=[3,3,3]. minAdm=7. pivot p=1. t1=Text2=1. r1=Text1-Text2=2, c1=Wext1-Text2=2.
# boundary1: K 1x1, X 2x1, N 1x2, E 2x2 ((0,0) FIXED=1, other 3 free), W 2x3. leaf Rfin2 1x3 (3 free).
# flatDim = 3*3+3*3 = 18. Coords: u(1)+K(1)+X(2)+N(2)+E-free(3)+W(6)+leaf(3) = 18. SQUARE.
u=sp.Symbol('u',real=True)
K=sp.Matrix([[sp.Symbol('K',real=True)]])
X=sp.Matrix(2,1, lambda i,j: sp.Symbol(f'X{i}',real=True))
N=sp.Matrix(1,2, lambda i,j: sp.Symbol(f'N{j}',real=True))
# E 2x2: (0,0)=1 fixed; (0,1),(1,0),(1,1) free
E=sp.Matrix([[sp.Integer(1), sp.Symbol('E01',real=True)],[sp.Symbol('E10',real=True), sp.Symbol('E11',real=True)]])
W=sp.Matrix(2,3, lambda i,j: sp.Symbol(f'W{i}{j}',real=True))
lf=sp.Matrix(1,3, lambda i,j: sp.Symbol(f'lf{j}',real=True))
# Bmat1 = [K; X*K] (Text1=3 x Text2=1). chainQ(N1)=[I_1|N1]=1x3.
Bmat1=sp.Matrix.vstack(K, X*K)        # 3x1
qN1=sp.Matrix.hstack(sp.eye(1), N)    # 1x3
# Rmat1 = rmatPad(E): 3x3, E in bottom-right 2x2 (rows 1,2 cols 1,2)
R1=sp.zeros(3,3)
for i in range(2):
    for j in range(2): R1[1+i,1+j]=E[i,j]
C2=u*lf; C1=Bmat1*qN1+u*R1; A0=C1
A1=sp.Matrix.vstack(C2 - N*W, W)      # kept 1 row + lift 2 rows = 3 x 3
phi=[sp.expand(e) for A in (A0,A1) for e in A]
allv=[u,K[0,0],X[0,0],X[1,0],N[0,0],N[0,1],E[0,1],E[1,0],E[1,1],
      W[0,0],W[0,1],W[0,2],W[1,0],W[1,1],W[1,2],lf[0,0],lf[0,1],lf[0,2]]
print("(3,3,3) Fix B: #coords=",len(allv)," flatDim=18 square:",len(allv)==18)
# full det
J=sp.Matrix(phi).jacobian(sp.Matrix(allv))
sub={v:sp.Rational(random.randint(1,9),random.randint(1,5)) for v in allv if v!=u}
Pf=sp.Poly(sp.expand(J.subs(sub).det()),u)
print("  full det u-degree=",Pf.degree()," (minAdm-1=6) monomial?",len(Pf.terms())==1)
# active = {u} ∪ {E-free: E01,E10,E11} ∪ {leaf: lf0,lf1,lf2}. card = 1+3+3 = 7 = minAdm.
Eidx=[allv.index(E[0,1]),allv.index(E[1,0]),allv.index(E[1,1])]
lfidx=[allv.index(lf[0,0]),allv.index(lf[0,1]),allv.index(lf[0,2])]
active=set([0]+Eidx+lfidx)
print("  active card =",len(active)," (minAdm=7):",len(active)==7)
def pbo(active,p,vec): return [vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(len(vec))]
Jrad=sp.Poly(sp.expand(sp.Matrix(pbo(active,0,allv)).jacobian(sp.Matrix(allv)).det()),u)
print("  radial(pivotBlowupOn active) det u-degree=",Jrad.degree()," (=minAdm-1=6):",Jrad.degree()==6)
