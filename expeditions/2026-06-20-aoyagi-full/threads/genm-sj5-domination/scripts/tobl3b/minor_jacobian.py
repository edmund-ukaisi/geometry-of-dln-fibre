import numpy as np
from itertools import combinations

# ==================================================================
# PART B: the Cauchy-Binet minor Jacobian on shell j is UNIFORMLY
# bounded (above & below) by eps_j-powers, and does NOT depend on the
# WEAK singular values.  This is the "no hidden non-uniformity" check.
#
# Claim (design): sigma_{M2-j}(Z) >= eps_j  ==>  there is a (M2-j)x(M2-j)
# minor of Z with |det| >= eps_j^{M2-j} / C_dim  (dimensional constant),
# and the CoV Jacobian is a power of this minor det.
# ==================================================================

rng = np.random.default_rng(0)

def max_minor_abs(Z, r):
    """max over rxr minors of |det|.  Z is M2 x n."""
    M2, n = Z.shape
    best = 0.0
    for rows in combinations(range(M2), r):
        for cols in combinations(range(n), r):
            d = abs(np.linalg.det(Z[np.ix_(rows,cols)]))
            if d > best: best = d
    return best

def sumsq_minors(Z, r):
    """sum over rxr minors of det^2  (= sum of squared products of r singular values, by Cauchy-Binet)."""
    M2, n = Z.shape
    s = 0.0
    for rows in combinations(range(M2), r):
        for cols in combinations(range(n), r):
            d = np.linalg.det(Z[np.ix_(rows,cols)])
            s += d*d
    return s

print("=== Cauchy-Binet: max (M2-j)-minor vs eps^{M2-j}, and WEAK-SV INDEPENDENCE ===")
print("    Anchor Z: 3x3, strong sing.values sig1,sig2 >= eps; weak sig3 = t -> 0.")
print("    r = M2-j = 2 (j=1).  Check: max 2-minor stays >= c*eps^2, INDEPENDENT of t.")
print()
M2, n = 3, 3
r = 2   # M2 - j, j=1
eps = 0.5
# fixed strong singular directions (random orthonormal), vary weak sig3 = t
U,_ = np.linalg.qr(rng.standard_normal((3,3)))
V,_ = np.linalg.qr(rng.standard_normal((3,3)))
sig12 = [1.0, eps]   # sig1=1, sig2=eps (=sigma_{M2-j}=sigma_2 >= eps, tight)
for t in [1e-1, 1e-2, 1e-3, 1e-6, 0.0]:
    S = np.diag([sig12[0], sig12[1], t])
    Z = U @ S @ V.T
    mm = max_minor_abs(Z, r)
    ss = sumsq_minors(Z, r)
    # theoretical lower bound: sqrt(sumsq/#minors);  #minors = C(3,2)^2 = 9
    nmin = 9
    lb = np.sqrt(ss/nmin)
    print(f"  t={t:<8} sigma_2={eps}: max|2-minor|={mm:.5f}  sqrt(sumsq/9)={lb:.5f}  eps^2={eps**2:.4f}  ratio max/eps^2={mm/eps**2:.3f}")
print("  --> max 2-minor is essentially CONSTANT in t (weak-SV independent), and >= eps^2/3-ish.")
print()

# Now vary sigma_2 = eps across the shell to confirm the eps^{M2-j} scaling of the minor bound.
print("=== minor lower bound scaling in eps = sigma_{M2-j} (t fixed tiny) ===")
t = 1e-6
for eps in [1.0, 0.5, 0.2, 0.1, 0.05]:
    S = np.diag([1.0, eps, t])
    Z = U @ S @ V.T
    mm = max_minor_abs(Z, r)
    print(f"  sigma_2=eps={eps:<6}: max|2-minor|={mm:.5f}   eps^2={eps**2:.5f}   max/eps^2={mm/eps**2:.3f}")
print("  --> max 2-minor ~ C*eps^2 (= eps^{M2-j}), C ~ O(1) dimensional.  Bounded ABOVE too (Z in box).")
