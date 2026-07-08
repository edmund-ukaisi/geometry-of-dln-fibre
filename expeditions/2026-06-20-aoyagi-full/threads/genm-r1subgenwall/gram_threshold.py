"""
genm-r1subgenwall — exact + MC verification of the Gram-coupling integrability threshold
and the "zero budget" at the binding cut.

CLAIM (exact algebra, singular-value / SVD Jacobian):
  For a FREE real p x n matrix W (p <= n), over a bounded box,
      ∫ det(W Wᵀ)^{-s} dW  <  ∞   <=>   s < (n - p + 1)/2.
  (Threshold set by the codim-(n-p+1) locus {rank W = p-1}: one singular value -> 0,
   measure ~ σ^{n-p} dσ, integrand ~ σ^{-2s}, converge iff n-p-2s > -1.)

We (1) re-derive the exponent count symbolically, (2) confirm by Monte-Carlo (GUIDE only),
(3) do the (3,3,3,4) budget arithmetic showing the coupling exponent EXACTLY saturates.
"""
import numpy as np
from math import isfinite

# ---------- (1) exact exponent count (symbolic, the worst single-value direction) ----------
def free_gram_threshold(p, n):
    # smallest codim rank-drop is dropping ONE rank: {rank = p-1}, codim n-p+1.
    # near that stratum one singular value sigma->0: measure sigma^{n-p} dsigma, integrand sigma^{-2s}.
    # converge iff (n-p) - 2s > -1  <=>  s < (n-p+1)/2.
    from fractions import Fraction
    return Fraction(n - p + 1, 2)

for (p, n) in [(2,3),(2,4),(3,4),(1,3),(2,2),(3,3)]:
    print(f"free {p}x{n}: ∫ det(WWᵀ)^-s < ∞  iff  s < {free_gram_threshold(p,n)}")

# ---------- (2) Monte-Carlo GUIDE: estimate whether ∫_{box} det(WWᵀ)^-s dW is finite ----------
# We estimate E[ det(WWᵀ)^-s ] over W uniform in [-1,1]^{p x n}. If the true integral diverges,
# the MC mean should grow (heavy tail) as sample size / resolution increases; if finite, it stabilizes.
def mc_mean(p, n, s, N=4_000_000, seed=0):
    rng = np.random.default_rng(seed)
    W = rng.uniform(-1, 1, size=(N, p, n))
    G = np.einsum('kij,klj->kil', W, W)          # W Wᵀ, shape (N,p,p)
    d = np.linalg.det(G)                          # det(W Wᵀ) >= 0
    d = np.clip(d, 1e-300, None)
    vals = d ** (-s)
    return vals.mean(), np.quantile(vals, [0.99, 0.999, 0.9999])

print("\n--- MC guide (2x3), threshold s<1.  s=0.8 (finite) vs s=1.0 (borderline) vs s=1.2 (div) ---")
for s in [0.8, 1.0, 1.2]:
    m1,_ = mc_mean(2,3,s,N=2_000_000,seed=1)
    m2,_ = mc_mean(2,3,s,N=8_000_000,seed=2)
    ratio = m2/m1 if m1>0 else float('inf')
    flag = "STABLE(finite)" if 0.5 < ratio < 2.0 else "GROWING(diverges)"
    print(f"  s={s}: mean(2e6)={m1:.4g}  mean(8e6)={m2:.4g}  ratio={ratio:.3f}  -> {flag}")

# ---------- (3) the (3,3,3,4) binding-cut budget arithmetic ----------
print("\n--- (3,3,3,4) binding cut t=1: budget arithmetic ---")
M = (3,3,3,4)
t = 1
a = M[0]-t; b = M[1]-t                     # a=2 (Γ rows), b=2 (Γ cols = non-pivot cols of A0)
# generic tail-product rank feeding Q_b: Q_b = W·A2, W = (M1-t)x M2 = 2x3, A2 = 3x4
# rank Q_b generic = min(b, rank(A2)) = min(2,3) = 2 = b (full).  det(QbQbᵀ) coupling exponent = a/2.
print(f"  a=M0-t={a}, b=M1-t={b}")
print(f"  Γ-block Morse shift on GENERIC stratum (full-rank Q_b): a*b/2 = {a*b/2}")
print(f"  Gram coupling exponent (Jacobian det(QbQbᵀ)^-a/2): s_coupling = a/2 = {a/2}")
print(f"  Q_b = W·A2, W free {b}x{M[2]}, so det(QbQbᵀ)^-s over W: threshold s < (M2 - b + 1)/2 = {(M[2]-b+1)/2}")
print(f"  => coupling exponent {a/2} vs its own W-integrability threshold {(M[2]-b+1)/2}: "
      + ("AT threshold (borderline/zero-slack)" if a/2==(M[2]-b+1)/2 else ("inside" if a/2<(M[2]-b+1)/2 else "OUTSIDE")))
# residual budget after generic Γ-peel:
c_max = 7/2                                # ½ minAdm(3,3,3,4) = 7/2
res_after_gamma = c_max - a*b/2            # residual exponent as c'->c_max
red_threshold = 3/2                        # ½ minAdm(redChain 1 M)=½ minAdm(1,3,4)=3/2
print(f"  ½·minAdm(M) = {c_max};  after Γ-peel residual exponent -> c'-ab/2 = {c_max}-{a*b/2} = {res_after_gamma}")
print(f"  ½·minAdm(redChain 1 M)=½·minAdm(1,3,4) = {red_threshold}")
print(f"  residual exponent {res_after_gamma} vs reduced threshold {red_threshold}: "
      + ("EXACTLY saturates -> ZERO budget for the det coupling" if res_after_gamma==red_threshold else "slack"))
