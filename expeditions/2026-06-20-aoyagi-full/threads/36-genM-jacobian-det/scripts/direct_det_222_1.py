import sympy as sp
# Question: is the det of x -> phiGen(x_p, B(x)) DIRECTLY computable (no bridge), if B is a full-rank decoder?
# phiGen = paramsEquivFlat(chartParamsGen), chartParamsGen_s = reindex(chain.A_s). The flat map outputs the
# layer-A entries. A_s = chainA(N_s)(W_s)(C_{s+1}); C_s = B_s*chainQ(N_s) + u*R_s; C_L = u*Rfin.
# For a FULL-RANK decoder, the output (A_0,...,A_{L-1} entries) must depend bijectively-enough on x.
#
# The (2,2,1) GENUINE chart (my §4b) was: A1=[[u0],[u0*u1]], A0=free. That IS a phiGen-style chart IF we can
# realize it as chartParamsGen for SOME B. Let me check: is the genuine (2,2,1) chart's layers expressible as
# chain.A_s for a full-rank B_det? The chain A_s = chainA(...). For (2,2,1): L=2, A_0:2x2, A_1:2x1.
# Genuine: A_1 = [[u0],[u0*u1]] (deepest, the u-carrier), A_0 = [[u2,u3],[u4,u5]] free.
# Chain: A_1 = chainA(N_1)(W_1)(C_2), C_2 = u*Rfin(2). For A_1 to be [[u0],[u0*u1]] = u0*[[1],[u1]], need
#   C_2 = u*Rfin with the chainA producing u0*[[1],[u1]]. chainA(N)(W)(C) with C=C_2 (the residual).
# This shows the DET chart's layers CAN be chain layers, IF B_det encodes the blow-up (fixed-1 + nonzero Rfin).
# That is EXACTLY route A-revisited: fix Rfin (nonzero, fixed-1) so chartParamsGen IS the genuine det chart.
# Then rate = routeMCore_phiGen at B_det (banked, decoder-agnostic), det = direct Jacobian of phiGen(x_p,B_det(x)).
#
# Let me verify: can a fixed-1 Rfin + the chain machinery reproduce the genuine (2,2,1) det chart's full-rank map?
# The genuine map: x=(u0..u5) -> (A0 entries: u2,u3,u4,u5; A1 entries: u0, u0*u1). det = u0 (=|x_p|^{m-1}, m=2).
# If chartParamsGen with B_det gives EXACTLY these layers (as functions of x), the det is computed DIRECTLY.
# The obstruction in genBlkFlatStruct was Rfin=0 (=> A_1's u-carrier C_2=0 => dead). Fix: Rfin(2) = a fixed-1
# residual (so C_2 = u*[[1],[?]] carrying the pivot). Then A_1 = chainA gives u*[[1],[u1]]-like. FULL RANK.
print("Route A-revisited / 2a CONVERGE: fix B_det (nonzero Rfin w/ fixed-1 + pivot slot) so chartParamsGen IS")
print("the genuine full-rank det chart. Then:")
print(" - RATE = routeMCore_phiGen at B=B_det (BANKED, decoder-agnostic; re-check only hC0). NO bridge.")
print(" - DET = direct Jacobian of x -> phiGen(x_p, B_det(x)). The chart's layers are explicit in x.")
print("The KEY: routeMCore_phiGen holds for ANY B, so the rate is a banked-theorem application at B_det,")
print("NOT a composeFold=phi bridge. This sidesteps 2b's never-landing funext ENTIRELY.")
