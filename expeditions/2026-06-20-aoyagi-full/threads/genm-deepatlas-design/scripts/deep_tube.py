"""
Guide (MC, not load-bearing): tube-volume scaling of {rank Z <= s} in deep parameter space.
vol{ ||smallest (rho-s) singular values of Z|| <= eps } ~ eps^{codim}. Fit exponent, compare CR.
Also test a NON-comparable slice (one E-block tiny vs another) doesn't yield lower exponent.
"""
import numpy as np
from functools import lru_cache
np.random.seed(3)
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

def prod(Ls):
    Z=Ls[0]
    for L in Ls[1:]: Z=Z@L
    return Z

def sigma_tail(widths, s, N=200000):
    """MC: sample layers with entries ~ U[-1,1] (compact box), measure P(tail sv-energy <= eps^2) vs eps."""
    p=len(widths)-1; rho=min(widths)
    Ls=[np.random.uniform(-1,1,size=(N,widths[i],widths[i+1])) for i in range(p)]
    Z=Ls[0]
    for i in range(1,p): Z=np.einsum('nij,njk->nik',Z,Ls[i])
    sv=np.linalg.svd(Z,compute_uv=False)  # N x min(v0,vp)
    tail=sv[:,s:]  # the (rank>s) singular values that must ->0
    energy=np.sqrt((tail**2).sum(axis=1))
    return energy

for widths,s in [((2,2,2),0),((2,2,2),1),((3,3,3),1),((2,3,2),1),((2,2,3),0)]:
    en=sigma_tail(widths,s)
    # estimate exponent via P(energy<=eps) ~ eps^codim  =>  log-log slope
    eps=np.array([0.02,0.04,0.08,0.16])
    P=np.array([(en<=e).mean() for e in eps])
    mask=P>0
    if mask.sum()>=2:
        slope=np.polyfit(np.log(eps[mask]),np.log(P[mask]),1)[0]
    else:
        slope=float('nan')
    print(f"  widths={widths} s={s}: MC tube-exponent≈{slope:.2f}  CR={CR(widths,s)}")
