"""
DECORRELATED verification, part 4 -- NUMERICAL RLCT GUIDE (Monte-Carlo; a GUIDE, not a certificate).

Purpose: confirm the single-factor BOUNDARY behaves as predicted --
   r=1, k>=2  leaf  ~ single-factor (matches single-matrix determinantal RLCT via the FreeBilinear collapse),
   r=k=2      leaf  ~ genuine product-corank (RLCT is Aoyagi's, strictly below the single-factor value).

Method: for a nonneg polynomial f(theta) on a box, vol{ f < eps } ~ C * eps^{lambda} (|log eps|^{m-1}),
lambda = rlct(f) at the deepest point. We estimate lambda by the log-log slope of vol{f<eps} vs eps over a
mid-range of eps (avoiding the log factor's ends). Calibrated first on KNOWN-exact cases.

We sample theta uniform in [-1,1]^N, compute f, and estimate P(f<eps) (proportional to vol) at a grid of eps.
"""
import numpy as np
rng = np.random.default_rng(12345)
N = 4_000_000

def slope_estimate(f_samples, eps_grid):
    fr = np.array([np.mean(f_samples < e) for e in eps_grid])
    lg = np.log(eps_grid); lv = np.log(np.maximum(fr, 1e-12))
    # fit slope over the interior region where fr in a good range
    mask = (fr > 2e-4) & (fr < 5e-2)
    if mask.sum() < 3:
        mask = (fr > 1e-4) & (fr < 1e-1)
    A = np.vstack([lg[mask], np.ones(mask.sum())]).T
    sl,_ = np.linalg.lstsq(A, lv[mask], rcond=None)[0]
    return sl, fr

eps_grid = np.exp(np.linspace(np.log(1e-6), np.log(1e-1), 22))

print("=== CALIBRATION on known-exact RLCTs ===")
# (cal 1) single matrix A: m x n, f = det(A A^T) = |det|^2-ish. {rank<m} codim (n-m+1). rlct of det(AA^T)^... 
#   For f = det(AA^T) (a single poly), vol{f<eps}~eps^{(n-m+1)/2}? Let's check m=1,n=2: f=||a||^2 (a in R^2),
#   vol{||a||^2<eps} ~ eps^1 (2D disk area ~ eps). lambda=1. (rlct of ||a||^2 = 1.)
a = rng.uniform(-1,1,size=(N,2)); f = a[:,0]**2 + a[:,1]**2
sl,_ = slope_estimate(f, eps_grid); print(f"  ||a||^2, a in R^2 : slope~{sl:.3f}  (exact rlct = 1)")
# (cal 2) f = det of 2x2 A squared? use f=det(A)^2, A 2x2 in [-1,1]^4. {det=0} codim1, det~ generic, 
#   vol{det(A)^2<eps}=vol{|det A|<sqrt eps} ~ sqrt(eps) => lambda=1/2.
A = rng.uniform(-1,1,size=(N,2,2)); dd = (A[:,0,0]*A[:,1,1]-A[:,0,1]*A[:,1,0])**2
sl,_ = slope_estimate(dd, eps_grid); print(f"  det(A)^2, A 2x2 : slope~{sl:.3f}  (exact rlct = 1/2)")

print()
print("=== BOUNDARY TEST: disposal weight structure of the leaf  || Delta . C . Z ||^2 ===")
print("    (Z a free deep matrix here; core w omitted to isolate the disposal singularity)")
def leaf_f(r,k,M2,q,N):
    D = rng.uniform(-1,1,size=(N,r,k))
    C = rng.uniform(-1,1,size=(N,k,M2))
    Z = rng.uniform(-1,1,size=(N,M2,q))
    DCZ = np.einsum('nij,njk,nkl->nil', D, C, Z)
    return np.sum(DCZ**2, axis=(1,2))
# r=1,k=2: predicted single-factor (rank-1 DC -> FreeBilinear). 
for (r,k,M2,q,label) in [(1,2,2,2,"r=1,k=2 (LANE-1)"),
                         (2,1,2,2,"r=2,k=1 (LANE-1 tall)"),
                         (2,2,2,2,"r=2,k=2 (min>=2 WALL)"),
                         (2,2,3,2,"r=2,k=2,M2=3 (min>=2 WALL)")]:
    f = leaf_f(r,k,M2,q,N)
    sl,fr = slope_estimate(f, eps_grid)
    print(f"  {label:26s}: rlct(||DCZ||^2) slope ~ {sl:.3f}")
print()
print("  Interpretation: the leaf rlct = the exponent lambda s.t. int(||DCZ||^2)^{-c}<inf iff c<lambda.")
print("  Lane-1 (min<=1) leaves resolve via rank-1 FreeBilinear (single-factor); min>=2 is genuine product.")
