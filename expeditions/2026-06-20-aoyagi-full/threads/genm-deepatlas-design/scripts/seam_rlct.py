"""
Test whether the FE-seam lowers the per-stratum threshold below CR/2 (would break the C_k gate).
(1) (2,2,2) model f=|H|^2+|FE|^2 : analytic threshold 3/2=CR/2. Numeric confirm.
(2) tube exponent of {rank Z_deep=0} for deep chains via HIGH-precision MC (importance sample near 0).
    tube vol{ sum of squared tail-SVs <= eps^2 } ~ eps^{kappa}. Compare exponent to CR.
"""
import numpy as np
from functools import lru_cache
np.random.seed(7)
@lru_cache(maxsize=None)
def CR(w,s):
    v=tuple(w)
    if len(v)==2:
        v0,v1=v; return 0 if s>=min(v0,v1) else (v0-s)*(v1-s)
    a,b=v[-2],v[-1]; best=None
    for r in range(0,min(a,b)+1):
        val=(a-r)*(b-r)+(0 if r<=s else CR(v[:-2]+(r,),s))
        if best is None or val<best: best=val
    return best

# (1) f=|H|^2+|FE|^2, H in R^2, F in R^2, E in R:  int_{[0,1]^5} f^{-q}, threshold?
def thresh_model(q,N=4_000_000):
    H=np.random.uniform(-1,1,(N,2)); F=np.random.uniform(-1,1,(N,2)); E=np.random.uniform(-1,1,(N,1))
    f=(H**2).sum(1)+((F**2).sum(1))*(E[:,0]**2)
    val=f**(-q)
    return val.mean(), np.isfinite(val).all()
print("=== (2,2,2) model f=|H|^2+|FE|^2, threshold should be 3/2 ===")
for q in [1.2,1.4,1.49,1.55,1.7]:
    m,_=thresh_model(q); print(f"  q={q}: E[f^-q]≈{m:.3g}  ({'finite-ish' if m<1e3 else 'BLOWING UP'})")

# (2) tube exponent, better MC: sample in a SMALL box (scale small so near-degenerate more frequent),
#     and use many eps points + regression on log-log with small eps.
def prod_batch(Ls):
    Z=Ls[0]
    for L in Ls[1:]: Z=np.einsum('nij,njk->nik',Z,L)
    return Z
def tube_exp(widths,s,N=6_000_000,box=1.0):
    p=len(widths)-1
    Ls=[np.random.uniform(-box,box,size=(N,widths[i],widths[i+1])) for i in range(p)]
    Z=prod_batch(Ls)
    sv=np.linalg.svd(Z,compute_uv=False)
    tail=sv[:,s:]
    en=np.sqrt((tail**2).sum(1))
    eps=np.array([0.005,0.01,0.02,0.04])
    P=np.array([(en<=e).mean() for e in eps])
    m=P>0
    slope=np.polyfit(np.log(eps[m]),np.log(P[m]),1)[0] if m.sum()>=2 else float('nan')
    return slope,P
print("\n=== tube exponent vs CR (small eps, 6M samples) ===")
for widths,s in [((2,2,2),0),((2,2,3),0),((3,2,3),0),((2,3,2),0),((2,2,2,2),0)]:
    sl,P=tube_exp(widths,s)
    print(f"  {widths} s={s}: tube-exp≈{sl:.2f}  CR={CR(widths,s)}   P={['%.2e'%x for x in P]}")
