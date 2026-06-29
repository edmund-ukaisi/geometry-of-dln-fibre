import sympy as sp
# CLEAN Fix B affine-radial split at (2,2,2). 
u,K,X,N,W0,W1,lf0,lf1 = sp.symbols('u K X N W0 W1 lf0 lf1', real=True)
allv=[u,K,X,N,W0,W1,lf0,lf1]
# Full chart phi (Fix B): out = [K, KN, KX, KNX+u, -NW0+u*lf0, -NW1+u*lf1, W0, W1]
phi=[K, K*N, K*X, K*N*X+u, -N*W0+u*lf0, -N*W1+u*lf1, W0, W1]
# radialAffine = pivotBlowupOn({lf0,lf1}, u): u->u; lf_i->u*lf_i; rest fixed. (idx: u=0, lf0=6, lf1=7)
def pbo(active,p,vec): return [vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(len(vec))]
R = pbo({6,7}, 0, allv)   # = [u,K,X,N,W0,W1, u*lf0, u*lf1]
# B in w-coords: out = [wK, wK wN, wK wX, wK wN wX + wu, -wN wW0 + wlf0, -wN wW1 + wlf1, wW0, wW1]
#   (E(0,0) reads wu additively; leaf reads wlf DIRECTLY -- already blown).
w=sp.symbols('w0:8',real=True)  # w0=wu,w1=wK,w2=wX,w3=wN,w4=wW0,w5=wW1,w6=wlf0,w7=wlf1
B=[w[1], w[1]*w[3], w[1]*w[2], w[1]*w[3]*w[2]+w[0], -w[3]*w[4]+w[6], -w[3]*w[5]+w[7], w[4], w[5]]
# check phi = B ∘ R: substitute w_i = R_i
BR=[sp.expand(e.subs({w[i]:R[i] for i in range(8)})) for e in B]
ok=all(sp.simplify(BR[i]-phi[i])==0 for i in range(8))
print("(2,2,2) Fix B: phi == B ∘ radialAffine?", ok)
JB=sp.Matrix(B).jacobian(sp.Matrix(list(w)))
detB=sp.factor(JB.det())
Jrad=sp.factor(sp.Matrix(pbo({6,7},0,allv)).jacobian(sp.Matrix(allv)).det())
print("  det DB =", detB, "(engine=K^2, u-free:",w[0] not in detB.free_symbols,")")
print("  det D(radialAffine) =", Jrad, "(= u^{minAdm-1}=u^2)")
print("  product =", sp.factor(detB.subs({w[1]:K})*Jrad), " vs full chart det K^2 u^2")
print()
print("KEY: radialAffine = pivotBlowupOn on the LEAF coords ONLY (NOT the E-block). The E(0,0) fixed-1")
print("  gives the ADDITIVE +u in B's output[3]; B reads it from the pivot slot wu. B is FULL RANK (K^2).")
print("  The map identity HOLDS as pivotBlowupOn on {leaf}, p=structPivot. NO affine-radial NEEDED for R!")
print("  R = pure pivotBlowupOn({leaf}, p); the additive u is ABSORBED INTO B (B is affine in wu).")
