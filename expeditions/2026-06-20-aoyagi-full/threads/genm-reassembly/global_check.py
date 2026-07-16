import numpy as np
rng=np.random.default_rng(1)
# Global: is ∫_{(A2,A_cor)∈box} ||A_cor A2||^{-a} finite for (4,4,4,4) a=1? = charge-only proxy for ∫frontCharge.
# Estimate small-ball RLCT lambda of loss=||A_cor A2||^2 over full (A2,A_cor); charge ||.||^{-a}=loss^{-a/2} integrable iff a/2<lambda.
# Also directly: truncated ∫ over box, check convergence (stable as we resolve small loss).
def sample(N):
    A2=rng.uniform(-1,1,size=(N,4,4))
    Ac=rng.uniform(-1,1,size=(N,1,4))
    prod=Ac@A2
    return np.sum(prod*prod,axis=(1,2))   # loss=||A_cor A2||^2
N=8_000_000
loss=sample(N)
eps=np.array([1e-1,1e-2,1e-3,1e-4,1e-5])
V=np.array([np.mean(loss<e) for e in eps])           # V(eps)=P(loss<eps) ~ eps^lambda
sl=(np.log(V[1:])-np.log(V[:-1]))/(np.log(eps[1:])-np.log(eps[:-1]))
print("small-ball P(loss<eps):",np.round(V,7))
print("local slopes -> lambda(||A_cor A2||^2):",np.round(sl,3))
lam=sl[-1]
print(f"charge a=1 -> need a/2=0.5 < lambda; lambda≈{lam:.2f} -> charge integrable = {0.5<lam}")
# direct truncated integral of charge ||.||^{-1}, box vol = 2^{16}*2^4
vol=2.0**(16+4)
Ts=[vol*np.mean(np.where(loss>e, loss**(-0.5), 0.0)) for e in eps]
print("truncated ∫ charge (eps=1e-1..1e-5):",np.round(Ts,1),"  (stabilizes -> finite)")
