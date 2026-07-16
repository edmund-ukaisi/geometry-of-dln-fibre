"""(D) a≥u FULLER lemma (keep transverse). Full C-integral, C:a×u:
 G_full = ∫_{C∈box^{a×u}}(W+frobSq(C·Q̃ₚ+M0))^{-c'}dC, M0=γ⊗Q_b.
CoV Y=C·Q̃ₚ (Jacobian det(Q̃ₚQ̃ₚᵀ)^{-a/2}, a copies of the u-Gram) + Y shift-invariance:
 G_full = det(Q̃ₚQ̃ₚᵀ)^{-a/2}·(W+‖M0⊥‖²)^{au/2-c'}·B_{au},  M0⊥ = M0 off rowspace(Q̃ₚ).
Charge au/2 (not a/2); det-Gram = the REDUCED chain's own structure (IH); NO ‖v‖^{-a} (so a≥u OK, unlike
the dropped-transverse R2 whose ∫‖v‖^{-a}dω diverges for a≥u). Verified ratio ~const within each case."""
import numpy as np
def G_full(W,Qtp,M0,cp,N=3_000_000):
    a,u=M0.shape[0],Qtp.shape[0]; C=np.random.uniform(-1,1,(N,a,u))
    E=np.einsum('nij,jk->nik',C,Qtp)+M0[None]; return ((W+(E**2).sum((-1,-2)))**(-cp)).mean()*(2**(a*u))
def pred(W,Qtp,M0,cp):
    a,u=M0.shape[0],Qtp.shape[0]; G=Qtp@Qtp.T
    Prow=Qtp.T@np.linalg.inv(G)@Qtp; Wp=W+((M0-M0@Prow)**2).sum()
    return np.linalg.det(G)**(-a/2)*Wp**(a*u/2-cp)
np.random.seed(0)
for (a,u,n) in [(2,1,2),(2,2,3),(3,1,2)]:
    Qtp=np.random.standard_normal((u,n)); M0=np.random.standard_normal((a,n)); cp=a*u/2+0.4
    for W in [1e-2,1e-4]:
        print(f"a={a} u={u}: G_full/pred = {G_full(W,Qtp,M0,cp)/pred(W,Qtp,M0,cp):.3f} (const-within-case ⟹ CoV OK)")
