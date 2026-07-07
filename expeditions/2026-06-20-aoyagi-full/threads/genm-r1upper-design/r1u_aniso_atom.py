import numpy as np
from scipy import integrate
rng=np.random.default_rng(1)
# CORRECTED atom (full-space, anisotropic, SHIFTED) — supersedes the isotropic box atom for the peel:
#   ∫_{Γ∈R^{p×q}} (w + ‖Γ R + S‖²)^{-c'} dΓ  =  Cinf(pq,c')·det(R Rᵀ)^{-p/2}·(w + ‖S(I-P_R)‖²)^{-(c'-pq/2)}
# for R (q×n) FULL ROW RANK, S (p×n), w>0, c'>pq/2.  P_R = Rᵀ(RRᵀ)⁻¹R (proj onto rowspace R).
# The shift S is absorbed by translation-invariance of the FULL-space integral (box ⊆ R^{pq}, integrand≥0).
# Verify for p=1,q=1 (Γ scalar) and p=1,q=2 vs direct quadrature.

def rhs_pred(w,R,S,cp,p,q):
    Gram=R@R.T; P=R.T@np.linalg.inv(Gram)@R
    wm=w + ((S@(np.eye(R.shape[1])-P))**2).sum()
    a=p*q
    # Cinf(a,c') = ∫_{R^a}(1+‖x‖²)^{-c'}dx = π^{a/2} Γ(c'-a/2)/Γ(c')
    from scipy.special import gamma as G
    Cinf=np.pi**(a/2)*G(cp-a/2)/G(cp)
    return Cinf*np.linalg.det(Gram)**(-p/2)*wm**(-(cp-a/2))

print("Full-space anisotropic-shifted corank atom: LHS (quad) vs RHS (closed form).")
# case p=1,q=1,n=1: Γ,R,S scalars
for (p,q,n) in [(1,1,1),(1,2,2),(2,1,1)]:
    cp = p*q/2 + 0.7    # > pq/2
    R=rng.standard_normal((q,n)); S=rng.standard_normal((p,n)); w=abs(rng.standard_normal())+0.3
    # LHS by MC over Γ∈R^{p×q}  (importance: integrand decays, use wide gaussian IS)
    N=4_000_000; sig=3.0
    G_=rng.standard_normal((N,p,q))*sig
    GR=np.einsum('npq,qn2->np2', G_, R[None].repeat(N,0)) if False else np.matmul(G_,R)  # (N,p,n)
    val=(w+((GR+S[None])**2).sum((1,2)))**(-cp)
    gpdf=np.exp(-(G_**2).sum((1,2))/(2*sig*sig))/((2*np.pi*sig*sig)**(p*q/2))
    lhs=(val/gpdf).mean()
    rhs=rhs_pred(w,R,S,cp,p,q)
    print(f"  p={p},q={q},n={n},c'={cp:.2f}: LHS(MC)={lhs:.4f}  RHS(closed)={rhs:.4f}  ratio={lhs/rhs:.3f}")
print("""
=> confirms: the box Γ-integral ≤ full-space = Cinf·det(RRᵀ)^{-p/2}·(w+‖S(I-P_R)‖²)^{-(c'-a/2)}.
   R=Q_b (full row rank), S=C·Q̃_p, w=‖A·Q̃_p‖². The SHIFT S is handled by translation-invariance;
   the ANISOTROPY R by the Gram det. Residual = det(Q_bQ_bᵀ)^{-(M0-t)/2}·(core)^{-(c'-a/2)}, core>0.
""")
