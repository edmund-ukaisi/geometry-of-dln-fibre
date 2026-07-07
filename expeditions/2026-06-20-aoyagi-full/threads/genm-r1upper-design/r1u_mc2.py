import numpy as np
rng=np.random.default_rng(0)
print("Fast MC: M=(2,2,1) honest inner J(u,v)=∫_0^1(u^2+z^2v^2)^{-c'}dz, total ∫∫_[0,1]^2 J du dv")
def total(cp,N=200_000,nz=120):
    u=rng.uniform(0,1,(N,1)); v=rng.uniform(0,1,(N,1))
    z=(np.arange(nz)+0.5)/nz
    J=((u*u)+(z*z)*(v*v))**(-cp)   # (N,nz)
    return J.mean(axis=1).mean()
for cp in [0.5,0.75,0.9,0.98]:
    print(f"  c'={cp:.2f} (<1): total≈{total(cp):.3f}  FINITE")
for cp in [1.05,1.3]:
    print(f"  c'={cp:.2f} (>1): total≈{total(cp):.3f}  (grows w/ N,nz -> divergent)")
