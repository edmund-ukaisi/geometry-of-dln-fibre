import sympy as sp
# ACTUAL R1 decoder at (2,2,2): pivot p=1, E-block(0,0)=1 FIXED, leaf carries the rerouted slot.
# flatDim=8. Coords (faithful): u=x0 (radial, read at structPivot). 
#   boundary 1 frame: K=x1, X=x2, N=x3 (the K/X/N roles, all free). E-block (1x1) is FIXED=1 (NOT a coord).
#   W1 (1x2) = x4,x5. leaf Rfin2 (1x2) = x6,x7 (the live leaf, the rerouted budget). Total free: u,K,X,N,W0,W1,lf0,lf1 = 8. SQUARE.
u,K,X,N,W0,W1,lf0,lf1 = sp.symbols('u K X N W0 W1 lf0 lf1', real=True)
def Rmat_pivot(u_scale):  # the u*Rmat1 at the pivot: E-block (0,0) = 1 (fixed) -> u_scale*1
    return sp.Matrix([[0,0],[0, u_scale*1]])   # rmatPad(pivotEIndicator)*u_scale, (1,1) entry = u_scale
Bmat1=sp.Matrix([[K],[X*K]]); qN1=sp.Matrix([[1,N]])
W=sp.Matrix([[W0,W1]]); lf=sp.Matrix([[lf0,lf1]])
def chart(u_scale, leaf_scale):
    R1u = Rmat_pivot(u_scale)          # u*Rmat: (1,1)=u_scale (the FIXED 1 scaled)
    C2 = leaf_scale*lf                 # u*Rfin leaf
    C1 = Bmat1*qN1 + R1u               # 2x2
    A0=C1
    A1=sp.Matrix.vstack(C2 - N*W, W)
    return [sp.expand(e) for A in (A0,A1) for e in A]
phi = chart(u, u)   # full chart: u multiplies BOTH the fixed-1 E-block AND the leaf
allv=[u,K,X,N,W0,W1,lf0,lf1]
print("FIX B R1 (2,2,2): #coords=",len(allv)," flatDim=8 -> square:",len(allv)==8)
J=sp.Matrix(phi).jacobian(sp.Matrix(allv))
detfull=sp.factor(J.det())
print("  FULL chart det =", detfull, "  (expect ± u^{minAdm-1}=u^2 * engine)")
# The radial direction: u multiplies (a) the fixed-1 E-block -> additive u*1=u (NO coord blown), 
#   (b) the leaf coords -> multiplicative u*lf0, u*lf1.
# AFFINE-RADIAL map: y_u = u; the E(0,0) slot has NO free coord (it's the literal 1, contributes u additively);
#   leaf actives: lf_i -> u*lf_i. So the "active" multiplicative set = {leaf coords} only (card = leaf_slots).
#   The pivot u itself contributes the ADDITIVE u at the E(0,0) position of the OUTPUT.
# radialAffine on coords (u, K,X,N,W,lf): u->u; lf_i -> u*lf_i; others fixed. (pivotBlowupOn on {lf0,lf1} by u)
# BUT the additive u·1 at E(0,0) is NOT produced by blowing up a coord -- it's a SEPARATE additive output.
# Let me compute det of pivotBlowupOn({lf0,lf1}, u) and see what's left for B.
def pbo(active_idx, p_idx, vec):
    return [vec[p_idx] if i==p_idx else (vec[p_idx]*vec[i] if i in active_idx else vec[i]) for i in range(len(vec))]
xv=sp.Matrix(allv); pidx=0; active={6,7}  # lf0=idx6, lf1=idx7
Jrad=sp.factor(sp.Matrix(pbo(active,pidx,xv)).jacobian(xv).det())
print("  pivotBlowupOn({lf0,lf1},u) det =", Jrad, " (card 3 incl pivot -> u^2). minAdm-1=2.")
print("  -> the MULTIPLICATIVE radial blows up ONLY the 2 leaf coords (card 3 w/ pivot = minAdm).")
print("  -> the E(0,0) additive u*1 is the SEPARATE additive piece (handled by B's affine structure).")
