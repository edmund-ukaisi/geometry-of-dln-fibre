import sympy as sp
# Construct the affine-radial map for Fix B and test phi = B ∘ radialAffine + det.
# Coords v=(u,K,X,N,W0,W1,lf0,lf1). 
# The radial map R: blows up the LEAF actives by u (lf_i -> u*lf_i), keeps u, K,X,N,W fixed.
#   R is pivotBlowupOn({lf0,lf1}, u) -- det = u^{card-1} = u^{3-1} = u^2 = u^{minAdm-1}. (minAdm=3)
# Then B(w) := the chart written in the blown coords, where:
#   - leaf outputs read the blown leaf coord w_lf directly (= u*lf, the multiplicative part);
#   - the E(0,0) additive output reads w_u (= u, the pivot) directly via the FIXED 1: u*1 = w_u.
# So B is: phi with u->w_u everywhere EXCEPT u*lf_i -> w_lf_i (blown). Let me build B and check B(R(v)) = phi(v).
u,K,X,N,W0,W1,lf0,lf1 = sp.symbols('u K X N W0 W1 lf0 lf1', real=True)
allv=[u,K,X,N,W0,W1,lf0,lf1]
Bmat1=sp.Matrix([[K],[X*K]]); qN1=sp.Matrix([[1,N]]); W=sp.Matrix([[W0,W1]]); lf=sp.Matrix([[lf0,lf1]])
def chart_coords(uval, leafmat):
    R1u=sp.Matrix([[0,0],[0,uval]])  # u*1 at E(0,0); uval = the u-scaling of the fixed 1
    C2=leafmat                        # the leaf block (already u-scaled or not)
    C1=Bmat1*qN1+R1u
    A0=C1; A1=sp.Matrix.vstack(C2 - N*W, W)
    return [sp.expand(e) for A in (A0,A1) for e in A]
# phi: uval=u (the fixed 1 scaled by u), leaf = u*lf
phi=chart_coords(u, u*lf)
# B: read in blown coords w. The additive E(0,0) is w_u (the pivot output = u*1 = w_u). leaf = w_lf (already blown).
wu,wK,wX,wN,wW0,wW1,wlf0,wlf1 = sp.symbols('wu wK wX wN wW0 wW1 wlf0 wlf1', real=True)
wlf=sp.Matrix([[wlf0,wlf1]])
# B uses uval = wu (the additive pivot), leaf = wlf (the blown leaf, NOT further scaled)
B=chart_coords(wu, wlf)
# substitute w with the K/X/N/W (un-blown) and leaf (blown): B is a function of w; compose with R(v):
# R(v): wu=u, wK=K, wX=X, wN=N, wW0=W0, wW1=W1, wlf0=u*lf0, wlf1=u*lf1.
Rsub={wu:u, wK:K, wX:X, wN:N, wW0:W0, wW1:W1, wlf0:u*lf0, wlf1:u*lf1}
BR=[sp.expand(e.subs(Rsub)) for e in B]
ok=all(sp.simplify(BR[i]-phi[i])==0 for i in range(8))
print("Fix B: phi == B ∘ radialAffine (radialAffine = pivotBlowupOn on LEAF coords)?", ok)
# det of radialAffine = pivotBlowupOn({lf0,lf1},u): u^2 = u^{minAdm-1}. (computed before)
# det DB: B in w-coords, jacobian wrt w:
wv=[wu,wK,wX,wN,wW0,wW1,wlf0,wlf1]
JB=sp.Matrix(B).jacobian(sp.Matrix(wv))
detB=sp.factor(JB.det())
print("  det DB =", detB, " (expect engine = K^2, u-free?", wu not in detB.free_symbols,")")
print("  det Dphi = det DB * det Drad =", detB, "* u^2 =", sp.factor(detB*u**2), " (matches full K^2 u^2)")
