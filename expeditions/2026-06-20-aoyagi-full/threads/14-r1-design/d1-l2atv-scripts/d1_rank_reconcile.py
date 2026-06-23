import numpy as np
# RECONCILE rank(dP)=9 vs nReg=8. What does rank(dP) count? dP: 27-dim perturbation → 9-dim output (3x3).
# rank(dP) ≤ 9 (output dim). rank(dP)=9 means dP is SURJECTIVE onto all 3x3 matrices — i.e. F=‖∏C−B‖²
# has a FULL-RANK Hessian-direction (every output direction is hit). But then the "core" (singular part)
# would be 0-dimensional, contradicting the existence of a homogeneous core at rank patterns.
#
# The resolution: nReg = r(M¹+M^{L+1})−r² is NOT rank(dP). nReg is the count of REGULAR GENERATORS in
# the SPLIT — but the split's regular block is NOT the full image of dP. Let me reconsider what L2-at-v
# actually splits.
#
# Actually: F = ‖∏C − B‖². The gradient ∇F = 0 at the optimal v (since ∏C=B, the residual is 0, so F=0
# is the MINIMUM, gradient 0). So the LINEAR part of F (not of ∏C) is ZERO at v — F has a critical point!
# F = ‖∏C−B‖² = ‖dP(δ) + O(δ²)‖² = ‖dP(δ)‖² + O(δ³). So F's quadratic part is ‖dP(δ)‖², a quadratic form
# of rank = rank(dP) = 9. The regular (Morse) block of F = the rank of its HESSIAN = rank of ‖dP(δ)‖²
# as a quadratic form = rank(dP) = 9? No — the Hessian of ‖dP(δ)‖² is dP^T dP, rank = rank(dP) = 9.
print("KEY CORRECTION: at the optimal v, ∏C=B so F=‖∏C−B‖²=0 is the MINIMUM ⟹ ∇F=0 (critical point).")
print("  F has NO linear part at v (it's a minimum). F = ‖dP(δ)‖² + O(δ³), quadratic part rank = rank(dP).")
print("  The regular (Morse) block = rank of the Hessian dP^T dP = rank(dP).")
print()
# So I had the structure WRONG. The controller's framing said "at v the core has a NONZERO LINEAR PART"
# — that's the linear part of the PRODUCT map ∏C (dP≠0), NOT of the loss F (∇F=0 at the minimum).
# The loss F is a SUM OF SQUARES with a critical point at v. Its Hessian rank = rank(dP) = nReg_actual.
# Let me recompute nReg_actual = rank(dP) and see if it's r(M¹+M^{L+1})−r² or something else.
W=3; r=2; L=3
np.random.seed(7)
C1=np.random.randn(W,W); C2=np.random.randn(W,W); B=np.diag([1.,1.,0.])
C3=B@np.linalg.inv(C2@C1)
# dP(δ) = C3C2 δ1 + C3 δ2 C1 + δ3 C2C1. Build the 9x27 matrix.
def vec(M): return M.flatten()
cols=[]
for k in range(27):
    d=np.zeros(27); d[k]=1
    D1=d[0:9].reshape(3,3); D2=d[9:18].reshape(3,3); D3=d[18:27].reshape(3,3)
    dPk = C3@C2@D1 + C3@D2@C1 + D3@C2@C1
    cols.append(vec(dPk))
M_dP = np.array(cols).T  # 9 x 27
rank_dP = np.linalg.matrix_rank(M_dP, tol=1e-9)
print(f"rank(dP) = {rank_dP}")
print(f"  candidate formulas: r(M¹+M^L⁺¹)−r² = {r*(W+W)-r*r}; full output = {W*W};")
print(f"    M^1·M^2 - (M^1-r)(M^2-r) type? The image of dP = tangent to the rank-≤? locus.")
# The image of dP at a rank-r point of the determinantal-type product = the tangent space to the
# {rank ≤ ...} variety. For ∏C with product rank r in M^1 x M^{L+1}, the rank-≤r locus tangent has
# codim (M^1-r)(M^{L+1}-r). So rank(dP) = M^1·M^{L+1} - (M^1-r)(M^{L+1}-r) = r(M^1+M^{L+1})-r² = nReg!
print(f"  rank-≤r tangent: M¹M^L⁺¹-(M¹-r)(M^L⁺¹-r) = {W*W-(W-r)*(W-r)} = r(M¹+M^L⁺¹)-r² = {r*(W+W)-r*r}")
print(f"  So EXPECTED rank(dP)=8 (the rank-≤2 locus tangent), but I got {rank_dP}. Investigate the gap.")
