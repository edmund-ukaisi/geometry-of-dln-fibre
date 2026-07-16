import numpy as np
rng = np.random.default_rng(0)

def det_gram_integral_growth(b, rho, a, N=4_000_000):
    """MC estimate of  ∫_{[-1,1]^{b×rho}} det(B Bᵀ)^{-a/2} · 1{det>δ} dB  as δ→0.
    If it GROWS ~ log(1/δ) the full integral (δ→0) DIVERGES; if it plateaus it converges.
    Integrable at origin iff  a < rho - b + 1  (i.e. -a/2 exponent, codim rho-b+1)."""
    B = rng.uniform(-1, 1, size=(N, b, rho))
    G = B @ np.transpose(B, (0,2,1))          # b×b Gram
    det = np.linalg.det(G)
    det = np.clip(det, 1e-300, None)
    vol = 2.0**(b*rho)                         # box volume
    w = det**(-a/2.0)
    for delta in [1e-1,1e-2,1e-3,1e-4,1e-6,1e-8]:
        mask = det > delta
        est = vol * w[mask].mean() * mask.mean()
        print(f"    delta={delta:.0e}  truncated-integral ≈ {est:12.4f}")
    return

for (b,rho) in [(2,3),(2,4)]:
    edge_a = rho - b + 1
    print(f"\n=== b={b}, rho={rho}:  edge a = rho-b+1 = {edge_a} ===")
    for a in [edge_a-1, edge_a]:
        tag = "EDGE (a=rho-b+1)" if a==edge_a else "interior (a<rho-b+1)"
        print(f"  a={a}  [{tag}]  exponent det^(-{a/2})")
        det_gram_integral_growth(b,rho,a)
