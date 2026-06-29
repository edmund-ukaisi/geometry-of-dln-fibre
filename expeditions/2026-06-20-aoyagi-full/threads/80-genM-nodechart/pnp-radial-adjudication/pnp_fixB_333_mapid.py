import sympy as sp, random
random.seed(7)
u=sp.Symbol('u',real=True)
Ksym=sp.Symbol('K',real=True)
X0,X1=sp.symbols('X0 X1',real=True); N0,N1=sp.symbols('N0 N1',real=True)
E01,E10,E11=sp.symbols('E01 E10 E11',real=True)
Wij=sp.symbols('W00 W01 W02 W10 W11 W12',real=True)
lf0,lf1,lf2=sp.symbols('lf0 lf1 lf2',real=True)
allv=[u,Ksym,X0,X1,N0,N1,E01,E10,E11,*Wij,lf0,lf1,lf2]
def build_chart(uscale_E, uscale_leaf, Efixed=sp.Integer(1)):
    # uscale_E: multiplier on the E-block (in chart = u; the (0,0) is the FIXED Efixed * uscale_E)
    K=sp.Matrix([[Ksym]]); X=sp.Matrix([[X0],[X1]]); N=sp.Matrix([[N0,N1]])
    W=sp.Matrix([[Wij[0],Wij[1],Wij[2]],[Wij[3],Wij[4],Wij[5]]]); lf=sp.Matrix([[lf0,lf1,lf2]])
    Bmat1=sp.Matrix.vstack(K,X*K); qN1=sp.Matrix.hstack(sp.eye(1),N)
    R1=sp.zeros(3,3)
    # E-block: (0,0)=Efixed, others free; ALL scaled by uscale_E in the chart
    Eblk=sp.Matrix([[Efixed, E01],[E10,E11]])
    for i in range(2):
        for j in range(2): R1[1+i,1+j]=uscale_E*Eblk[i,j]
    C2=uscale_leaf*lf; C1=Bmat1*qN1+R1; A0=C1; A1=sp.Matrix.vstack(C2-N*W,W)
    return [sp.expand(e) for A in (A0,A1) for e in A]
phi=build_chart(u, u)   # chart: u scales E-block AND leaf
# active = {u} ∪ {E01,E10,E11, lf0,lf1,lf2}
Eidx=[allv.index(E01),allv.index(E10),allv.index(E11)]; lfidx=[allv.index(lf0),allv.index(lf1),allv.index(lf2)]
active=set([0]+Eidx+lfidx)
def pbo(active,p,vec): return [vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(len(vec))]
R=pbo(active,0,allv)   # u->u; E_free->u*E_free; leaf->u*leaf
# B in w-coords: chart with E-block (0,0)=u-additive (=wu), E-free read directly (wE), leaf read directly (wlf).
#   i.e. B = build_chart with uscale_E=1 on the FREE E entries, but the (0,0) FIXED term scaled by wu.
# Construct B(w): the E-block in B = [[wu*1, wE01],[wE10,wE11]] (the (0,0) gets wu additive; free read direct),
#   leaf = wlf direct.  Then B(R(allv)) should = phi.
w=sp.symbols('w0:18',real=True)
def build_B(wv):
    wu=wv[0]; wK=wv[1]; wX=sp.Matrix([[wv[2]],[wv[3]]]); wN=sp.Matrix([[wv[4],wv[5]]])
    wE01,wE10,wE11=wv[6],wv[7],wv[8]; wW=sp.Matrix([[wv[9],wv[10],wv[11]],[wv[12],wv[13],wv[14]]])
    wlf=sp.Matrix([[wv[15],wv[16],wv[17]]])
    Bmat1=sp.Matrix.vstack(sp.Matrix([[wK]]), wX*wK); qN1=sp.Matrix.hstack(sp.eye(1),wN)
    R1=sp.zeros(3,3)
    Eblk=sp.Matrix([[wu, wE01],[wE10,wE11]])  # (0,0)=wu (additive pivot), free read DIRECT (no u)
    for i in range(2):
        for j in range(2): R1[1+i,1+j]=Eblk[i,j]
    C2=wlf; C1=Bmat1*qN1+R1; A0=C1; A1=sp.Matrix.vstack(C2-wN*wW,wW)
    return [sp.expand(e) for A in (A0,A1) for e in A]
B=build_B(w)
BR=[sp.expand(e.subs({w[i]:R[i] for i in range(18)})) for e in B]
ok=all(sp.simplify(BR[i]-phi[i])==0 for i in range(18))
print("(3,3,3) Fix B: phi == B ∘ pivotBlowupOn(active={pivot,E-free,leaf})?", ok)
JB=sp.Matrix(B).jacobian(sp.Matrix(list(w)))
sub={w[i]:sp.Rational(random.randint(1,9),random.randint(1,5)) for i in range(1,18)}  # w0=wu kept symbolic
detB=sp.factor(JB.subs(sub).det())
print("  det DB (wu symbolic) =", detB, " | wu in det?", w[0] in detB.free_symbols, "(want u-free)")
# engine at (3,3,3): |K|^{r+c} = |K|^{2+2}=K^4. det DB should = K^4 (up to sign).
