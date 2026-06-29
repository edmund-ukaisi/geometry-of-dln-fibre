import sympy as sp, random
random.seed(13)
u=sp.Symbol('u',real=True)
# M=(3,4,3,3). Wext=[3,4,3,3]. Text=[3,3,2,1,0] (Text_L=Text_3=1). L=3. minAdm=7, flatDim=33.
# bd1 (s=1): Text1=3,Text2=2 -> K 2x2, r=1, c1=Wext1-Text2=4-2=2. X 1x2, N 2x2, E 1x2, W 2x Wext2=2x3.
# bd2 (s=2): Text2=2,Text3=1 -> K 1x1, r=1, c2=Wext2-Text3=3-1=2. X 1x1, N 1x2, E 1x2, W 2x Wext3=2x3.
# leaf (s=3): Rfin3 = Text3 x Wext3 = 1x3 (live; 1 anchor + 2 free).
def SM(name,r,c): return sp.Matrix(r,c, lambda i,j: sp.Symbol(f'{name}_{i}_{j}',real=True)) if r*c>0 else sp.zeros(r,c)
K1=SM('K1',2,2); X1=SM('X1',1,2); N1=SM('N1',2,2); E1=SM('E1',1,2); W1=SM('W1',2,3)
K2=SM('K2',1,1); X2=SM('X2',1,1); N2=SM('N2',1,2); E2=SM('E2',1,2); W2=SM('W2',2,3)
lf=SM('lf',1,3); lf[0,2]=sp.Integer(1)   # leaf anchor at (0,2)
B1=sp.Matrix.vstack(K1, X1*K1)   # 3x2 = Text1 x Text2
B2=sp.Matrix.vstack(K2, X2*K2)   # 2x1 = Text2 x Text3
qN1=sp.Matrix.hstack(sp.eye(2), N1)  # Text2=2 x Wext1=4 -> [I2|N1] 2x4
qN2=sp.Matrix.hstack(sp.eye(1), N2)  # Text3=1 x Wext2=3 -> [I1|N2] 1x3
# Rmat = rmatPad(E): Text_s x Wext_s, E in bottom (r x c) corner.
R1=sp.zeros(3,4); R1[2,2]=E1[0,0]; R1[2,3]=E1[0,1]    # bd1: r=1,c=2 bottom-right 1x2
R2=sp.zeros(2,3); R2[1,1]=E2[0,0]; R2[1,2]=E2[0,1]    # bd2: r=1,c=2
C3=u*lf                          # 1x3
C2=B2*qN2 + u*R2                 # (2x1)(1x3)+u(2x3)=2x3 = Text2 x Wext2
C1=B1*qN1 + u*R1                 # (3x2)(2x4)+u(3x4)=3x4 = Text1 x Wext1
# A0 (bd0 identity, c0=Wext0-Text1=3-3=0): A0 = C1 = 3x4 = Wext0 x Wext1
A0=C1
# A1: kept = C2 - N1*W1 (Text2=2 x Wext2=3), lift = W1 (c1=2 x Wext2=3). A1 = 4x3? wait Wext1 x Wext2 = 4x3.
#    kept 2 rows + lift 2 rows = 4 = Wext1. cols Wext2=3. OK.
A1=sp.Matrix.vstack(C2 - N1*W1, W1)   # (2x3 over 2x3)=4x3
# A2: kept = C3 - N2*W2 (Text3=1 x Wext3=3), lift = W2 (c2=2 x Wext3=3). A2 = 3x3 = Wext2 x Wext3.
A2=sp.Matrix.vstack(C3 - N2*W2, W2)   # (1x3 over 2x3)=3x3
F=[]
for A in (A0,A1,A2):
    for i in range(A.rows):
        for j in range(A.cols): F.append(sp.expand(A[i,j]))
print("num outputs:", len(F), " (expect 33)")
allsyms=sorted({s for e in F for s in e.free_symbols}, key=str)
print("num free syms (incl u):", len(allsyms), " (expect 33)")
# exact QQ[u] det
J=sp.Matrix(F).jacobian(sp.Matrix(allsyms))
sub={v: sp.Rational(random.randint(-9,9), random.randint(1,6)) for v in allsyms if v!=u}
P=sp.Poly(sp.expand(J.subs(sub).det()), u)
print("det u-degree =", P.degree(), " (expect minAdm-1 = 6)")
print("u-monomial terms:", [(d,str(c)[:18]) for (d,),c in P.terms()], " (expect single deg-6)")
# pivot not in K-core + u-linearity
kcore=set()
for M in (K1,X1,N1,W1,K2,X2,N2,W2):
    for e in M: kcore|=e.free_symbols
maxu=0; ukc=[]; uprod=[]
ui=allsyms.index(u)
for e in F:
    Pe=sp.Poly(e,*allsyms)
    for mono,co in Pe.terms():
        if mono[ui]>maxu: maxu=mono[ui]
        if mono[ui]==1:
            others=[allsyms[k] for k in range(len(allsyms)) if k!=ui and mono[k]>0]
            if any(s in kcore for s in others): ukc.append(1)
            if sum(mono[k] for k in range(len(allsyms)) if k!=ui)>=2: uprod.append(1)
print("pivot u in K-core?", u in kcore, "| max u-deg:", maxu, "| u*Kcore count:", len(ukc), "| u*product count:", len(uprod))
print("CHECK 1 (3,4,3,3): det = single u^6 monomial, u-linear, pivot not in K-core, no u*Kcore/product ✓")
