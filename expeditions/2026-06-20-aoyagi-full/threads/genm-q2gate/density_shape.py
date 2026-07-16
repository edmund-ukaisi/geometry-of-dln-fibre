import numpy as np
rng = np.random.default_rng(0)

# Estimate pushforward density rho(Y) of Y = P @ Z, P,Z uniform on [-1,1]^{2x2},
# via kernel counting in a small box around target Y0. Guiding-only (float).
# Discriminator: is rho ~ log(1/dist) (Codex) or ~ dist^{-A}, A>=1 (satred) ALONG the
# generic det=0 hypersurface (rank-one target), vs scaling toward the ORIGIN.

def sample_Y(n):
    P = rng.uniform(-1,1,size=(n,2,2))
    Z = rng.uniform(-1,1,size=(n,2,2))
    return np.einsum('nij,njk->nik', P, Z)

N = 40_000_000
Y = sample_Y(N)   # (N,2,2)
detY = Y[:,0,0]*Y[:,1,1]-Y[:,0,1]*Y[:,1,0]

# --- Test 1: density ALONG generic hypersurface (rank-one point, away from origin).
# Target a generic rank-one Y0 = [[1,0.3],[0.5,0.15]] (det=0, ||Y0|| ~ O(1)). Measure
# relative density in a slab {|det Y - s| small, Y near Y0's neighborhood} as s->0.
# Use: condition on Y being close to a line through a generic point, look at det distribution.
# Simpler robust test: histogram of |detY| density near 0 CONDITIONED on ||Y||_F in a mid band.
fro = np.sqrt((Y**2).sum(axis=(1,2)))
band = (fro>0.8)&(fro<1.2)          # away from origin: ||Y||~1
d = np.abs(detY[band])
print("=== Test 1: p(|det Y|) near 0, conditioned on ||Y||_F in [0.8,1.2] (generic hypersurface) ===")
edges = np.array([0,0.002,0.004,0.008,0.016,0.032,0.064,0.128])
h,_ = np.histogram(d, bins=edges)
mids = 0.5*(edges[:-1]+edges[1:])
widths = np.diff(edges)
dens = h/widths/band.sum()
for m,de in zip(mids,dens):
    print(f"  |det|~{m:.4f}: cond.density ~ {de:.3f}")
print("  (Codex: density of det -> CONSTANT or mild-log as det->0 [rho on Y bounded/log]; ")
print("   satred power A>=1 would show cond.density BLOWING UP as |det|->0.)")

# --- Test 2: scaling toward ORIGIN. rho(rX) for fixed direction X0 (invertible), r->0.
# Estimate rho at Y = r*X0 by counting samples in a box of half-width h*r (scale box with r)
# and dividing by box volume (2*h*r)^4. If rho(rX0) ~ r^{-A_scale}, then
# count/(vol) ~ r^{-A_scale}. Equivalently count ~ r^{4-A_scale}.
X0 = np.array([[1.0,0.2],[0.1,0.9]])   # invertible, sigma_max~1
print("\n=== Test 2: rho(r*X0) scaling toward origin (X0 invertible) ===")
print("   count in box halfwidth h*r about r*X0; rho_est = count / (2 h r)^4 / N")
h = 0.15
for r in [0.4,0.2,0.1,0.05,0.025]:
    center = r*X0
    hw = h*r
    inbox = np.all(np.abs(Y-center[None])< hw, axis=(1,2))
    cnt = inbox.sum()
    vol = (2*hw)**4
    rho_est = cnt/vol/N
    print(f"  r={r:.3f}: count={cnt:7d}  rho_est={rho_est:.4e}  r*rho_est={r*rho_est:.4e}  (const r*rho => A_scale=1)")

# --- Test 3: DIRECT sigma_min -> 0 at fixed sigma_max ~ 1 (the hypersurface shape).
# Discriminates rho ~ log(1/sigma_min) [alpha=0, Codex] vs rho ~ sigma_min^{-alpha} [alpha>0].
print("\n=== Test 3: rho(Y) as sigma_min(Y)->0 at sigma_max(Y)~1 (direction fixed) ===")
Ys = Y   # reuse
U = Y.reshape(-1,4)
svals = np.linalg.svd(Y, compute_uv=False)   # (N,2), descending
smax = svals[:,0]; smin = svals[:,1]
# condition sigma_max in [0.9,1.1]; bin by sigma_min, estimate conditional density of sigma_min
sel = (smax>0.9)&(smax<1.1)
sm = smin[sel]
edges = np.array([0.001,0.002,0.004,0.008,0.016,0.032,0.064,0.128,0.256])
h,_ = np.histogram(sm, bins=edges)
widths=np.diff(edges); mids=0.5*(edges[:-1]+edges[1:])
dens = h/widths/sel.sum()
prev=None
for m,de in zip(mids,dens):
    ratio = (de/prev) if prev else float('nan')
    print(f"  sigma_min~{m:.4f}: cond.density(sigma_min) ~ {de:6.3f}   ratio_to_prev={ratio:.3f}")
    prev=de
print("  [log/alpha=0 => density of sigma_min tends to CONSTANT as sigma_min->0")
print("   (uniform-ish); a genuine rho~sigma_min^{-alpha} would make it GROW like sigma_min^{-alpha}.]")
