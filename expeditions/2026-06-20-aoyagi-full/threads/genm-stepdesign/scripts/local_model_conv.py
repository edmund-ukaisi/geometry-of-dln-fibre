import numpy as np
rng=np.random.default_rng(11)
dim_y,kap,dim_w=4,1,2; N=dim_y+kap+dim_w
def loss(P):
    y=P[:,:dim_y]; t=P[:,dim_y:dim_y+kap]; w=P[:,dim_y+kap:]
    return np.sum(y**2,1)+np.sum(t**2,1)*np.sum(w**2,1)
def I(q,nS,R=1.0):
    P=rng.uniform(-R,R,size=(nS,N)); L=loss(P)
    L=np.maximum(L,1e-300)
    return (2*R)**N*np.mean(L**(-q))
print("# Analytic RLCT of |y|^2+t^2|w|^2 (dim_y=4,kappa=1,dim_w=2):")
print("#   component {y=0,t=0}: codim 5 -> 5/2 ; {y=0,w=0}: codim 6 -> 3 ; min = 5/2 = 2.5")
print("# Direct MC convergence: q<2.5 stabilizes; q>2.5 grows with N (divergent).")
for q in [2.3, 2.7]:
    ests=[I(q,n) for n in [200000,800000,3200000,12800000]]
    print(f"  q={q}: " + "  ".join(f"{e:.3e}" for e in ests) + ("  <-stable(finite)" if q<2.5 else "  <-growing(divergent)"))
