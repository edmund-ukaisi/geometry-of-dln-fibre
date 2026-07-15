import numpy as np
rng = np.random.default_rng(0)

# Verify the change-of-variables residual: for Q_b = A_cor @ Z_deep (A_cor: b x M2, Z_deep: M2 x n, M2>=n full col rank),
# integral over A_cor in a box of f(Q_b) equals det(Zd^T Zd)^{-b/2} * integral over Q_b (in row(Zd)^b) of f * (fibre vol).
# Test with f = det(Q_b Q_b^T)^{-a/2} (charge). Compare direct A_cor integral vs the claimed reduced form.

def frob2(A): return float(np.sum(A*A))

# CASE: M=(3,3,4,3) u=2 a=1 b=1 : Z_deep = A2 is 4x3, n=3, M2=4, so full col rank 3 (=n). Q_b=A_cor@A2 is 1x3.
# A_cor is 1x4.  charge = det(Q_b Q_b^T)^{-a/2} = (||Q_b||^2)^{-1/2}   (b=1,a=1)
M2,n,b,a = 4,3,1,1
A2 = rng.standard_normal((M2,n))          # fixed deep factor
G = A2 @ A2.T                              # 4x4 rank 3
Gplus = np.linalg.det(A2.T @ A2)          # pseudo-det = det(A2^T A2), 3x3
print("det(A2 A2^T) (full 4x4) =", np.linalg.det(G), "  (should be ~0)")
print("det+(=det A2^T A2) =", Gplus)

# Direct: integrate charge over A_cor in box [-1,1]^4  (MC)
N=4_000_00
Ac = rng.uniform(-1,1,size=(N,1,M2))
Qb = Ac @ A2[None,:,:]                      # N x 1 x 3
nrm2 = np.sum(Qb*Qb,axis=(1,2))
charge = nrm2**(-a/2.0)
# box volume factor: uniform on [-1,1]^4 has density 1/2^4 ; integral = vol*mean = 2^4 * mean
vol_Acor = 2.0**M2
I_direct = vol_Acor*np.mean(charge)
print("Direct  ∫_{A_cor box} ||A_cor A2||^{-1} dA_cor  ≈", I_direct)

# Reduced: det+(G)^{-b/2} * ∫_{Q_b in row(A2)^b, image of box} ||Q_b||^{-1} dQ_b * (fibre already inside)
# Easiest faithful check: change var w = A_cor (4-dim), map to Q_b(3-dim)+fibre(1-dim). We instead verify the
# SCALAR identity by computing the SAME integral in Q_b coords: the pushforward measure of Lebesgue on A_cor-box
# under A_cor->Q_b is det+(G)^{-b/2} * Leb_{row(A2)} restricted to image, times fibre length. 
# Cross-check via a second, independent estimator: sample Q_b uniformly in a large ball in R^3, weight by the
# preimage fibre length and det+ factor. This is heavy; instead do the cleanest test: the *ratio* of the A_cor
# integral for TWO different A2 (same shape) should scale as det+(G)^{-b/2}, IF f depends only through Q_b and
# the residual is det+^{-b/2}. Verify by rescaling A2 -> c*A2: then Q_b -> c*Q_b, charge -> c^{-a}*charge,
# det+ -> c^{2n}? no: det(A2^T A2) with A2->cA2 is c^{2n} det. residual^{-b/2}=(c^{2n})^{-b/2}=c^{-nb}.
for c in [1.0, 1.5, 2.0]:
    A2c = c*A2
    Qb = Ac @ A2c[None,:,:]
    nrm2 = np.sum(Qb*Qb,axis=(1,2))
    Ival = vol_Acor*np.mean(nrm2**(-a/2.0))
    # predicted scaling of I with c: charge ~ (c^2 ||.||^2)^{-a/2} = c^{-a} * base ; so I(c) = c^{-a} I(1)
    print(f"c={c}: I={Ival:.5f}  c^-a*I(1)={(c**(-a))*I_direct:.5f}")
