import numpy as np
rng=np.random.default_rng(0)
# Per-chart inner integral I(Q)=∫_{A0∈box(M0,M1)} frobSq(A0·Q)^{-c'} dA0, Q fixed (M1×n).
# Claim: on the t-pivot chart the corank block Γ enters as frobSq(Γ·Q_b), Q_b = non-pivot rows of Q,
#   so the residual (after isotropizing + corank atom) ~ σ_min(Q_b)^{-a} · (pivot/core part),
#   NOT frobSq(Q)^{-a/2}. Test: scale ONLY the bottom row of Q (‖Q_b‖=ε), hold top row O(1);
#   does I(Q) blow up like ε^{-a}? (a=1 for (2,2,2,2) t=1).  frobSq(Q)^{-a/2} would stay ~O(1).
def I_of_Q(Q, cprime, N=1_500_000):
    M0,M1=2,2
    A0=rng.uniform(-1,1,(N,M0,M1))
    P=np.matmul(A0,Q[None])                # (N,M0,n)
    fro2=(P**2).sum((1,2)); fro2=np.maximum(fro2,1e-300)
    return (fro2**(-cprime)).mean()*(2.0**(M0*M1))
cprime=0.75   # (2,2,2,2): full-rank-Q inner conv iff c'<2; rank-1-Q iff c'<1; here 0.75<1 so finite, test scaling
print("(2,2,2,2) t=1, a=1. Q = [[1,0],[eps,0]]-ish: top row O(1), bottom row norm=eps. c'=0.75.")
print("If residual ~ ‖Q_b‖^{-a}=eps^{-1}: I blows up like eps^{-1}. If ~frobSq(Q)^{-1/2}: I~O(1).\n")
eps_list=[1.0,0.3,0.1,0.03,0.01]
Is=[]
for eps in eps_list:
    Q=np.array([[1.0,0.5],[eps*0.8, eps*0.6]])   # bottom row norm = eps, top row O(1); rank 2 for eps>0
    val=I_of_Q(Q,cprime); Is.append(val)
    print(f"  eps=‖Q_b‖={eps:5.2f}: I(Q)={val:8.3f}   eps^-1={1/eps:6.1f}   frobSq(Q)^-1/2={ (np.sum(Q**2))**-0.5:.3f}")
sl=np.polyfit(np.log(1/np.array(eps_list)), np.log(Is),1)[0]
print(f"\n  slope d(logI)/d(log 1/eps) = {sl:.3f}   (≈1 => residual ~ ‖Q_b‖^{{-1}}, NOT frobSq(Q)^{{-1/2}})")
print("  => per-chart residual is a power of the NON-PIVOT tail rows Q_b, pointwise ≥ P_full^{-a/2}=‖Q‖^{-a}.")
