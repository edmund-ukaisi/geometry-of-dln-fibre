"""NUMERIC CONFIRMATION (a guide, not a certificate) that the decoupled corank weight
    Wenn(Z; a, b) = INT_{A_cor in [-1,1]^{b x M2}} det((A_cor Z)(A_cor Z)^T)^{-a/2}
DIVERGES for a rank-deficient deep factor Z (M2 x Mlast, Mlast < M2), at the sector
params a=a*, b=b*, where a*+b* = rho_Z + 1 (rho_Z = min(M2,Mlast) = rank).

Witness M=(2,3,3,2): a=1, b=2, M2=3, Mlast=2, Z 3x2 rank 2.  A_cor 2x3, A_cor*Z 2x2,
det((A_cor Z)(A_cor Z)^T)^{-1/2} = |det(A_cor Z)|^{-1}.  det(A_cor Z) is one polynomial,
codim-1 zero locus, so INT |det|^{-1} LOG-diverges.

We detect divergence by a truncated MC estimate with a shrinking floor eps on the base
|det|: if the estimate GROWS ~ log(1/eps) as eps->0, the integral diverges.  (Compare the
'full row-rank M2=3' hypothetical: Z 3x3 rank 3 -> A_cor*Z is 2x3, det of the 2x2 gram has
a codim-2 zero, INT converges; the estimate should STABILISE as eps->0.)
"""
import numpy as np

def wenn_estimate(Z, a, b, M2, N=4_000_000, floors=(1e-1,1e-2,1e-3,1e-4,1e-5,1e-6), seed=0):
    """MC estimate of INT_{[-1,1]^{b x M2}} det((A Z)(A Z)^T)^{-a/2}, with det floored at
    'floor' (i.e. base = max(det_gram, floor^?) ) to probe growth as floor->0.
    Volume of box = 2^{b*M2}."""
    rng = np.random.default_rng(seed)
    vol = 2.0 ** (b * M2)
    # sample A_cor uniform in [-1,1]^{b x M2}
    A = rng.uniform(-1.0, 1.0, size=(N, b, M2))
    AZ = np.einsum('nij,jk->nik', A, Z)      # N x b x Mlast
    gram = np.einsum('nik,njk->nij', AZ, AZ) # N x b x b
    detg = np.linalg.det(gram)               # N   (>=0)
    detg = np.clip(detg, 0, None)
    out = {}
    for fl in floors:
        base = np.maximum(detg, fl)          # floor the base determinant
        val = base ** (-(a) / 2.0)
        out[fl] = vol * val.mean()
    return out

if __name__ == "__main__":
    print("=== Witness M=(2,3,3,2): a=1,b=2,M2=3,Mlast=2 ; RANK-DEFICIENT deep factor ===")
    # A representative generic rank-2  3x2 Z (deep product of widths (3,2)):
    rng = np.random.default_rng(42)
    A2 = rng.normal(size=(3,2)); A3 = rng.normal(size=(2,2))
    Z_rankdef = A2 @ A3      # 3x2, rank 2 (= min(3,2)); as an M2 x Mlast = 3x2 object
    print("  Z shape", Z_rankdef.shape, "rank", np.linalg.matrix_rank(Z_rankdef))
    est = wenn_estimate(Z_rankdef, a=1, b=2, M2=3, N=3_000_000)
    prev=None
    for fl in sorted(est, reverse=True):
        growth = "" if prev is None else f"  (delta={est[fl]-prev:+.3f})"
        print(f"    floor={fl:.0e}:  Wenn_est = {est[fl]:8.3f}{growth}")
        prev=est[fl]
    print("  -> if estimate grows ~ linearly in log10(1/floor) => LOG-DIVERGENT.")
    print()

    print("=== CONTRAST: hypothetical FULL row-rank M2=3 deep factor (Z 3x3 rank 3) ===")
    print("    (would need Mlast>=3; not the real chain, just to show M2-frame WOULD converge)")
    Z_full = rng.normal(size=(3,3))    # 3x3 rank 3
    print("  Z shape", Z_full.shape, "rank", np.linalg.matrix_rank(Z_full))
    est2 = wenn_estimate(Z_full, a=1, b=2, M2=3, N=3_000_000)
    prev=None
    for fl in sorted(est2, reverse=True):
        growth = "" if prev is None else f"  (delta={est2[fl]-prev:+.3f})"
        print(f"    floor={fl:.0e}:  Wenn_est = {est2[fl]:8.3f}{growth}")
        prev=est2[fl]
    print("  -> should STABILISE (converges: a=1 < M2-b+1 = 2).")
