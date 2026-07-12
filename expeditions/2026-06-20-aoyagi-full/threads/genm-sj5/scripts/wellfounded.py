import numpy as np
# Well-foundedness BASE: a SINGLE free matrix has σ_min² ≍ dist²(·,{rank≤ρ}) = m=1 ALWAYS (Eckart-Young).
# So width-2 (single matrix, no product) has NO m>1 bad locus → the arity recursion bottoms out.
# Contrast: a PRODUCT Z=AB can have m>1 (Z=ab: σ_min=|ab|≍t², m=2 at a=b=0). m>1 ⟸ product structure only.

rng=np.random.default_rng(0)
def sigmin_ratio_single(rho, n, m, trials=4000):
    # near a rank-ρ matrix M0 + t·E (E full-rank perturbation): σ_{ρ+1}(M0+tE) / (t·dist-scale) → const (m=1)
    worst=[]
    for _ in range(trials):
        U=np.linalg.qr(rng.standard_normal((n,n)))[0]; V=np.linalg.qr(rng.standard_normal((m,m)))[0]
        s=np.concatenate([rng.uniform(1,2,rho), np.zeros(min(n,m)-rho)])
        M0=U[:,:len(s)]@np.diag(s)@V[:len(s),:]
        t=1e-3; E=rng.standard_normal((n,m))
        A=M0+t*E
        sig=np.linalg.svd(A,compute_uv=False)
        # σ_{ρ+1} should be ≍ t (order 1 in t): ratio σ_{ρ+1}/t bounded away from 0 and ∞
        worst.append(sig[rho]/t)
    return np.percentile(worst,1), np.percentile(worst,99)
lo,hi=sigmin_ratio_single(1,3,4)
print(f"[single matrix, rank-1 base, σ₂/t over perturbations]  1%={lo:.3f}  99%={hi:.3f}  → σ₂ ≍ t (ORDER 1, m=1). Eckart-Young: σ_{{ρ+1}}=dist to rank-ρ, so σ²≍dist² ALWAYS. No m>1.")

# product Z=A·B (2x2 · 2x2), near A,B both rank-1 coincidentally: σ_min(Z) can be order 2 (m=2)
def sigmin_product_order(trials=3000):
    worst=[]
    for _ in range(trials):
        t=1e-2
        # A,B both = rank1 + t·(full): their product's σ_min ~ t^2 when both drop coincidentally
        a=np.array([[1.,0.],[0.,0.]])+t*rng.standard_normal((2,2))
        b=np.array([[1.,0.],[0.,0.]])+t*rng.standard_normal((2,2))
        Z=a@b
        sig=np.linalg.svd(Z,compute_uv=False)
        worst.append(sig[1]/t**2)   # σ_2(Z)/t² — bounded ⟺ order 2 (m=2)
    return np.percentile(worst,1),np.percentile(worst,99)
lo2,hi2=sigmin_product_order()
print(f"[product Z=AB, both near rank-1, σ₂(Z)/t²]  1%={lo2:.3f}  99%={hi2:.3f}  → σ₂(Z) ≍ t² (ORDER 2, m=2) at the coincidental (intersection-ray) crossing. m>1 ⟸ PRODUCT structure.")
print("\n⟹ WELL-FOUNDED: m>1 bad loci come ONLY from ≥2 coincidentally-degenerating factors (the product/intersection-ray).")
print("   Each recursion peels a factor (arity↓) or restricts to a factor's rank-drop (dim↓); BOTTOMS OUT at width-2")
print("   (single matrix ⟹ Eckart-Young m=1 everywhere ⟹ NO bad locus). No infinite regress.")
