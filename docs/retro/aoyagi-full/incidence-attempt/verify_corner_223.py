import sympy as sp

# ============ Corner (i): M=(2,2,3), u=1,a=1,b=1,j=1, t*=0, T1=2 ============
# Z=I_3, Q_p=e1=(1,0,0), Qhat=e1, Vhat=[e2;e3], R=1.
# A_cor=(al,t2,t3), Q_b=A_cor=(al,t2,t3). X=Q_b Qhat^T=al ; Y=Q_b Vhat^T=(t2,t3).
# U=[P;C] (2x1), W=[B;Gp] (2x1).  freedSchurLoss = ||U R + W X||^2 + ||W Y||^2.
P,C,B,Gp,al,t2,t3 = sp.symbols('P C B Gp al t2 t3', real=True)
U = sp.Matrix([P,C]); W = sp.Matrix([B,Gp]); R=sp.Matrix([[1]]); X=sp.Matrix([[al]]); Y=sp.Matrix([[t2,t3]])
loss_coord = (U*R + W*X).norm()**2 + (W*Y).norm()**2
loss_coord = sp.expand(loss_coord)

# Direct freedSchurLoss form for cross-check: ||[P|B] hsQ||^2 + ||C Q_p + Gp Q_b||^2, hsQ=[Qp;Qb]
Qp = sp.Matrix([[1,0,0]]); Qb = sp.Matrix([[al,t2,t3]]); hsQ = Qp.col_join(Qb)
PB = sp.Matrix([[P,B]])
loss_direct = sp.expand((PB*hsQ).norm()**2 + (C*Qp + Gp*Qb).norm()**2)
print("coord form == direct form:", sp.simplify(loss_coord-loss_direct)==0)
print("loss =", loss_coord)

# Claimed explicit form: (P+al B)^2 + (C+al Gp)^2 + (B^2+Gp^2)(t2^2+t3^2)
claim = (P+al*B)**2 + (C+al*Gp)**2 + (B**2+Gp**2)*(t2**2+t3**2)
print("matches claimed explicit form:", sp.simplify(loss_coord-claim)==0)

# ---- Branch A (t=0, P=-al B, C=-al Gp; al,B,Gp O(1)) : transverse Hessian rank ----
# near generic point al=1,B=1,Gp=1: coords (xiP=P+B, xiC=C+Gp, t2,t3)
subs0 = {al:1, B:1, Gp:1}
xi1,xi2 = sp.symbols('xi1 xi2', real=True)
lossA = claim.subs({P: xi1 - al*B, C: xi2 - al*Gp}).subs(subs0)   # = xi1^2+xi2^2+2(t2^2+t3^2)
lossA = sp.expand(lossA)
H = sp.hessian(lossA, [xi1,xi2,t2,t3])
print("branchA Hessian (should be diag, rank 4):", H.rank(), "det", H.det())
# => integrable iff 2c' < 4 (nondeg quadratic in 4 vars): RLCT threshold c'<2 = T1.

# ---- Branch B (B=Gp=0, P=C=0, t free-but-shell) exact reduction ----
# loss = xi1^2+xi2^2 + (B^2+Gp^2)(t2^2+t3^2),  xi1=P+al B, xi2=C+al Gp.
# integrate (xi1,xi2)[2d] ~ M^{2-2c'}, M^2=(B^2+Gp^2)|t|^2 (for c'>1);
# then dB dGp: (B^2+Gp^2)^{1-c'} over 2d -> int rho^{3-2c'} drho conv iff c'<2;
# then dt: |t|^{2-2c'} over 2d -> int r^{3-2c'} dr conv iff c'<2.
print("branchB reduction: both dB dGp and dt integrals converge iff c'<2  (exponent 3-2c' > -1)")

# ---- Numeric finiteness guide: local integral of the FULL loss over a small box ----
import numpy as np
rng = np.random.default_rng(0)
def mc_local(cp, N=4_000_000, L=0.5, eps=0.5):
    # box: P,C,B,Gp in [-L,L]; al in [0.5,1.5]; t2,t3 in [-eps,eps] (shell proxy)
    Pv=rng.uniform(-L,L,N); Cv=rng.uniform(-L,L,N); Bv=rng.uniform(-L,L,N); Gv=rng.uniform(-L,L,N)
    alv=rng.uniform(0.5,1.5,N); t2v=rng.uniform(-eps,eps,N); t3v=rng.uniform(-eps,eps,N)
    loss = (Pv+alv*Bv)**2+(Cv+alv*Gv)**2+(Bv**2+Gv**2)*(t2v**2+t3v**2)
    vol = (2*L)**4 * 1.0 * (2*eps)**2
    val = np.mean(loss**(-cp))*vol
    return val
for cp in [1.5, 1.9, 1.95, 2.0, 2.05, 2.2]:
    print(f"  MC local integral c'={cp}: {mc_local(cp):.4g}")
