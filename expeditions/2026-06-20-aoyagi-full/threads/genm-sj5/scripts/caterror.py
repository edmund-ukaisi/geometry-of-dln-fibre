import numpy as np
# The hunt's counterexample: M(t)=[[1,t],[t,0]] — a SINGLE matrix, σ_min order-2 in the PARAMETER t.
for t in [1e-1,1e-2,1e-3,1e-4]:
    M=np.array([[1.,t],[t,0.]])
    sig=np.linalg.svd(M,compute_uv=False)
    print(f"t={t:.0e}: σ_min={sig[1]:.3e}  σ_min/t²={sig[1]/t**2:.3f}  det(MMᵀ)={np.linalg.det(M@M.T):.3e} (≈t⁴)")
print("⟹ σ_min ≈ t² : ORDER 2 in the parameter t, for a SINGLE 2×2 matrix.\n")
print("MY CATEGORY ERROR (§7 C): I claimed 'single matrix ⟹ m=1 by Eckart-Young'.")
print("  Eckart-Young: σ_min = matrix-DISTANCE to {rank≤1} — TRUE, but that is NOT the PARAMETER vanishing order.")
print("  Here the path t↦M(t) approaches {rank≤1} and σ_min = dist vanishes to ORDER 2 in t (tangential/constrained).")
print("  So m>1 is NOT 'product-only'; a single matrix (constrained entries / a path) can have order-2 σ_min.")
print("  ⟹ 'bottoms-out-at-width-2 (no bad locus)' is FALSE: the base's σ_min can itself be order-2.")
print("  [The width-2 RLCT base uses frobSq (ALL SVs, nondegenerate SoS, m=1) — fine; but the OFF-SECTOR")
print("   σ_min-tube analysis, which is what §7 built, is where the order-2 σ_min breaks the corank-recursion.]")
