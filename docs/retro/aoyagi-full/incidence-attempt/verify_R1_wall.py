import numpy as np
rng=np.random.default_rng(7)
# Mixed stratum (3,3,N=7) u=2 j=2 b=1: loss = ||U1||^2 + mu^2||U2||^2 + tau^2||W||^2, U*,W in R^3, tau in (0,eps) wt tau^{N-3}.
# T1=9/2. Decisive pair:
#   (b) mu>0 fixed: RLCT should be 9/2 (all 3 blocks nondeg).
#   (a) mu=0 limit (U2 freed, box-capped -> collapses to const): RLCT should DROP to 3.
# If lambda(a)=3 < lambda(b)=4.5, then Psi(mu) -> infinity as mu->0 for c' in (3, 4.5) -> POINTWISE (P) FAILS.
N=7
def lam_volume(sampler, boxvol, N_s=40_000_000, kmax=22):
    eps=np.array([2.0**-k for k in range(1,kmax)])
    a,w=sampler(N_s)   # a=loss values, w=importance weights
    V=np.array([np.sum(w*(a<e))/N_s*boxvol for e in eps])
    m=V> (30.0/N_s)*boxvol
    le,lv=np.log(eps[m]),np.log(V[m]); k=min(6,m.sum())
    return np.polyfit(le[-k:],lv[-k:],1)[0]

def samp_mu(mu):
    def f(Ns):
        U1=rng.uniform(-1,1,(Ns,3)); U2=rng.uniform(-1,1,(Ns,3)); W=rng.uniform(-1,1,(Ns,3))
        tau=rng.uniform(0,0.5,Ns)
        loss=(U1**2).sum(1)+mu**2*(U2**2).sum(1)+tau**2*(W**2).sum(1)
        wt=tau**(N-3)                # measure weight
        return loss, wt
    return f
boxvol=(2.0)**9*0.5
print("Mixed stratum (3,3,7) u=2 j=2 b=1, T1=4.5. RLCT lambda via sublevel volume:")
for mu in [0.3, 0.05, 0.0]:
    lam=lam_volume(samp_mu(mu), boxvol)
    tag="(mu>0: predict 4.5)" if mu>0 else "(mu=0 limit: predict 3 -> Psi blows up on (3,4.5))"
    print(f"   mu={mu}: lambda={lam:.3f}  {tag}")
