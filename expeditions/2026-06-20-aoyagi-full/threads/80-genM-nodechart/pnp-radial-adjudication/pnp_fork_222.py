import sympy as sp
# ACTUAL decoders at (2,2,2). Text=[2,2,1], Wext=[2,2,2]. minAdm=3. Single genuine boundary p=1 (k=0), leaf s=2.
# pivot boundary p=1: K 1x1, r1=Text1-Text2=1, c1=Wext1-Text2=1. E-block 1x1. leaf Rfin2: Text2 x Wext2 = 1x2.
#
# === FIX A: genBlkFlatLive (live pivot) — Rmat1 = rmatPad(readE), E FREE (multiplicative); leaf free. ===
# Coords: u=x0 (pivot). K=x1. X=x2(? r1*t1=1). N1=x_? . E1 free = one coord. W1 (c1 x Wext2=1x2). leaf (1x2 free).
# Use distinct symbols; structPivot = x0 read as the radial scalar (multiplies ALL Rmat/Rfin).
u=sp.Symbol('u',real=True)
K=sp.Symbol('K',real=True); X=sp.Symbol('X',real=True); N=sp.Symbol('N',real=True)
E=sp.Symbol('E',real=True)            # FIX A: E free
W=sp.Matrix([[sp.Symbol('W0',real=True),sp.Symbol('W1',real=True)]])  # 1x2
lf=sp.Matrix([[sp.Symbol('lf0',real=True),sp.Symbol('lf1',real=True)]])  # leaf 1x2 free
def chart(Eval, anchor_in_leaf=False, leaf=lf):
    # Bmat1 = [K; X*K] (Text1=2 x Text2=1). chainQ(N1)=[I_1|N1]=1x2 (t1=1,c1=1).
    Bmat1=sp.Matrix([[K],[X*K]])           # 2x1
    qN1=sp.Matrix([[1, N]])                # 1x2
    # Rmat1 = rmatPad(Eval): 2x2, Eval in bottom-right (r1 x c1 = 1x1 at (1,1)).
    R1=sp.Matrix([[0,0],[0,Eval]])
    C2=u*leaf                              # 1x2
    C1=Bmat1*qN1 + u*R1                    # 2x2
    A0=C1                                  # bd0 identity, c0=0
    # A1 = [C2 - N1*W1 ; W1]: kept t1=1 row (C2 - N*W), lift c1=1 row (W). 2x2.
    A1=sp.Matrix.vstack(C2 - N*W, W)
    return [sp.expand(e) for A in (A0,A1) for e in A]
# FIX A: E free
phiA=chart(E, leaf=lf)
allA=[u,K,X,N,E,W[0,0],W[0,1],lf[0,0],lf[0,1]]
print("FIX A (live pivot genBlkFlatLive): flatDim=8, #coords=",len(allA))
JA=sp.Matrix(phiA).jacobian(sp.Matrix(allA))
import random; random.seed(1)
subA={v:sp.Rational(random.randint(1,9),random.randint(1,5)) for v in allA if v!=u}
PA=sp.Poly(sp.expand(JA.subs(subA).det()),u)
print("  det u-poly =",PA.as_expr()," u-deg=",PA.degree()," (minAdm-1=2) monomial?",len(PA.terms())==1)
# FIX A active = {u} ∪ {E,lf0,lf1} = card 4? but minAdm=3! Check hslot count.
print("  Fix A: ALL R/Rfin free => active={u,E,lf0,lf1} card=4 != minAdm=3. COUNT MISMATCH risk.")
