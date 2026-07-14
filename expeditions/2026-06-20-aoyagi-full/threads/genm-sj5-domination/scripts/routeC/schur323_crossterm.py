import numpy as np
import sympy as sp

print("="*70)
print("(3,2,3) deep-layer Schur chart — exact-algebra checks")
print("="*70)

# ---------- (A) loss = tr(M G), M = A0^T A0 (2x2), G = A1 A1^T (2x2) ----------
A0 = sp.Matrix(3,2, lambda i,j: sp.Symbol(f'p{i}{j}'))   # 3x2 front
A1 = sp.Matrix(2,3, lambda i,j: sp.Symbol(f'q{i}{j}'))   # 2x3 deep
loss = sum((A0*A1)[i,j]**2 for i in range(3) for j in range(3))
M = A0.T*A0   # 2x2
G = A1*A1.T   # 2x2
trMG = sp.trace(M*G)
print("(A) loss == tr(M G):", sp.simplify(loss - trMG) == 0)

# ---------- (B) Schur / LU chart on A1: A1 = L U, L=[[1,0],[d/a,1]], pivot a=q00 ----------
a,b,c,d,e,f = sp.symbols('a b c d e f')
A1s = sp.Matrix([[a,b,c],[d,e,f]])
W1 = e - d*b/a; W2 = f - d*c/a          # Schur complement row W = (W1,W2)
U  = sp.Matrix([[a,b,c],[0,W1,W2]])
L  = sp.Matrix([[1,0],[d/a,1]])
print("(B) A1 == L*U  :", sp.simplify(A1s - L*U) == sp.zeros(2,3))
# CoV (e,f)->(W1,W2) at fixed (a,b,c,d): translation, Jacobian
J_ef_W = sp.Matrix([[sp.diff(W1,e),sp.diff(W1,f)],[sp.diff(W2,e),sp.diff(W2,f)]])
print("    Jacobian d(W1,W2)/d(e,f) =", J_ef_W.tolist(), " det =", sp.simplify(J_ef_W.det()),
      "(measure-preserving shear, NOT a det-power)")

# ---------- (C) loss in chart coords: front cols g=a1+(d/a)a2, a2 ; cross term ----------
g0,g1,g2, x0,x1,x2 = sp.symbols('g0 g1 g2 x0 x1 x2')   # g and a2 in R^3
g  = sp.Matrix([g0,g1,g2]); a2 = sp.Matrix([x0,x1,x2])
rho1 = sp.Matrix([[a,b,c]])          # row
wrow = sp.Matrix([[0,W1,W2]])        # row (0,W)
P = g*rho1 + a2*wrow                 # 3x3 product = A0 A1
loss_chart = sum(P[i,j]**2 for i in range(3) for j in range(3))
main = (rho1.dot(rho1))*(g.dot(g)) + (wrow.dot(wrow))*(a2.dot(a2))
cross = sp.expand(loss_chart - main)
cross_expected = 2*(g.dot(a2))*(rho1.dot(wrow.T))
print("(C) loss_chart - [ ||rho1||^2||g||^2 + ||w||^2||a2||^2 ] == 2<g,a2><rho1,w> :",
      sp.simplify(cross - cross_expected)==0)
print("    <rho1,w> = b*W1 + c*W2 (pivot entry a drops):",
      sp.simplify(rho1.dot(wrow.T) - (b*W1+c*W2))==0)

# ---------- (D) cross term is SIGN-INDEFINITE (block-additive surrogate is NOT a one-sided bound) ----------
rng = np.random.default_rng(0)
signs=set(); worst_ratio=0.0
for _ in range(200000):
    gg=rng.normal(size=3); aa=rng.normal(size=3)
    r1=rng.normal(size=3); ww=np.array([0.0,*rng.normal(size=2)])
    Pn=np.outer(gg,r1)+np.outer(aa,ww)
    Ln=(Pn**2).sum()
    mainn=(r1@r1)*(gg@gg)+(ww@ww)*(aa@aa)
    cr=Ln-mainn
    signs.add(np.sign(round(cr,9)))
    # ratio |cross|/main can exceed 1 -> cancellation
    if mainn>1e-6: worst_ratio=max(worst_ratio, abs(cr)/mainn)
print("(D) observed signs of cross term:", sorted(signs),
      " -> sign-indefinite" if len(signs)>1 else " -> definite")
print("    max |cross|/main observed:", round(worst_ratio,3),
      "(>1 => loss can be < block-additive main; also loss can be driven toward 0)")

# can loss be ~0 while main is bounded away from 0?  (cancellation => not lower-boundable by main)
minloss_over_main=1e9
for _ in range(400000):
    gg=rng.normal(size=3)
    r1=rng.normal(size=3)
    # pick a2 anti-aligned, w to cancel:  loss = ||g r1 + a2 w||^2, choose a2 w ~ -g r1
    # take w with support (0,*), a2 arbitrary
    ww=np.array([0.0,*rng.normal(size=2)])
    aa=rng.normal(size=3)
    Pn=np.outer(gg,r1)+np.outer(aa,ww)
    Ln=(Pn**2).sum()
    mainn=(r1@r1)*(gg@gg)+(ww@ww)*(aa@aa)
    if mainn>1e-3:
        minloss_over_main=min(minloss_over_main, Ln/mainn)
print("    min loss/main observed:", round(minloss_over_main,4),
      "(near 0 => NO constant k>0 with loss >= k*main; qPeel block-additive form unreachable by domination)")
