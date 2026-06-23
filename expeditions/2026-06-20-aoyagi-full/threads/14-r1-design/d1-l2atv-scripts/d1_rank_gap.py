import numpy as np
# WHY rank(dP)=9 not 8? dP(δ) = C3C2·δ1 + C3·δ2·C1 + δ3·C2C1. The image of dP should be the tangent
# to {products of rank ≤ ?} at B. But the relevant variety is the IMAGE of the multiplication map
# μ(C1,C2,C3)=C3C2C1, whose image is ALL matrices of rank ≤ min(widths)=3 (no constraint!) since the
# C's are FULL 3x3 — the product can be ANY 3x3 matrix (rank up to 3). So the image of μ is all of
# 3x3 (dim 9), and dP is surjective (rank 9) at a GENERIC point. The rank-r CONSTRAINT only bites if
# the WIDTHS force it (a narrow bottleneck layer), not here (all widths 3 ≥ r=2).
#
# THE REAL POINT: nReg = r(M¹+M^{L+1})−r² is the regular block at the DEEPEST point of the CORE (where
# the bottleneck IS r — the reduced widths M=H−r). At a general optimal v with FULL widths (no bottleneck),
# the product map is a SUBMERSION (rank 9), so F=‖∏C−B‖² is MORSE (rank-9 Hessian, NO singular core)!
print("RESOLUTION of the rank gap (the real structure):")
print("""
  With FULL widths (all 3 ≥ r=2) and B rank 2, the multiplication map μ(C)=C3C2C1 is a SUBMERSION at v
  (its image is all 3x3 matrices, rank dP=9). So F=‖μ−B‖² is MORSE at v — Hessian rank 9, NO singular
  core. The learning coefficient at THIS v = 9/2 (pure regular). This is a SMOOTH optimal point.

  The SINGULAR core only appears when a BOTTLENECK forces the product rank below the widths — i.e. the
  reduced-width core M=H−r where the product is FORCED to rank 0 at the deepest point. THAT is where the
  cascade/hnode lives (the core), and where nReg=r(M¹+M^{L+1})−r² is the regular count.
""")
# So the L2-at-v split's structure: at a general optimal v, F is Morse in the dP-image (rank = the
# product map's rank at v), and the CORE is the kernel directions where the product is bottleneck-forced.
# The split peels the Morse block (rank dP) — the regular generators. The pivots are units (the product
# sub-blocks). Confirm: the regular block dim = rank(dP), variable with v's rank pattern, all unit-pivot.
W=3; r=2
np.random.seed(7)
C1=np.random.randn(W,W); C2=np.random.randn(W,W); B=np.diag([1.,1.,0.]); C3=B@np.linalg.inv(C2@C1)
# At THIS v (full widths), rank dP=9 ⟹ Morse, no core. The CORE case needs a bottleneck. Build one:
# M=(3,3,3,3) but with a rank-2 BOTTLENECK at an interior layer (C2 rank 2) so the product is forced ≤2.
C2b = np.random.randn(W,W); U,s,Vt=np.linalg.svd(C2b); s[2]=0; C2b=U@np.diag(s)@Vt  # rank 2
C21b = C2b@C1
# product C3·C2b·C1: to make it = B (rank 2), need C3 s.t. C3·(C2b C1)=B. C2bC1 rank 2, use pseudo-inverse:
C3b = B @ np.linalg.pinv(C21b)
prodb = C3b@C2b@C1
print(f"bottleneck v (C2 rank 2): product=B? {np.allclose(prodb,B,atol=1e-6)}, rank={np.linalg.matrix_rank(prodb)}")
cols=[]
for k in range(27):
    d=np.zeros(27); d[k]=1
    D1=d[0:9].reshape(3,3); D2=d[9:18].reshape(3,3); D3=d[18:27].reshape(3,3)
    dPk=C3b@C2b@D1 + C3b@D2@C1 + D3@C2b@C1
    cols.append(dPk.flatten())
rank_dPb=np.linalg.matrix_rank(np.array(cols).T, tol=1e-7)
print(f"  rank(dP) at bottleneck v = {rank_dPb}  (nReg=r(M¹+M^L⁺¹)-r²={r*(W+W)-r*r} if bottleneck forces it)")
print()
print("⟹ the regular block dim = rank(dP) at v, which DEPENDS on v's bottleneck/rank structure. The")
print("  L2-at-v split peels exactly this Morse block (unit pivots = the product sub-blocks at v). The")
print("  residual core = the bottleneck-forced singular directions. At full-width Morse v, core is empty.")
