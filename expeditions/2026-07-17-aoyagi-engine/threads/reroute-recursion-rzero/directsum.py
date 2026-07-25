#!/usr/bin/env python3
"""Verify RLCT direct-sum additivity + the coupled-term behavior on SMALL (reliable) models.
Key: does the coupled x^2 y^2 block UNDERCUT when summed with clean squares, or does additivity hold?
Also compute exact rlct of the P2 local model R_local = xi1^2+xi2^2+d2^2+(d1 mu)^2 (expect 2)."""
import numpy as np
rng=np.random.default_rng(1)
def rlct_mc(f,dim,N=6000000,sig=1.0):
    X=rng.normal(0,sig,size=(N,dim)); L=np.sort(f(X))
    ts=np.exp(np.linspace(np.log(L[80]),np.log(np.quantile(L,0.04)),14))
    lg=[(np.log(t),np.log(np.count_nonzero(L<t)/N)) for t in ts]
    lg=np.array([p for p in lg if np.isfinite(p[1])]); k=max(len(lg)//2,3)
    return np.polyfit(lg[:k,0],lg[:k,1],1)[0]
tests=[
 ("x^2 (expect .5)",         lambda X:X[:,0]**2,1,0.5),
 ("x^2+y^2 (expect 1)",      lambda X:(X[:,:2]**2).sum(1),2,1.0),
 ("x^2 y^2 (expect .5)",     lambda X:(X[:,0]*X[:,1])**2,2,0.5),
 ("x^2+y^2z^2 (dsum->1)",    lambda X:X[:,0]**2+(X[:,1]*X[:,2])**2,3,1.0),
 ("x^2+y^2+(zw)^2 (->1.5)",  lambda X:X[:,0]**2+X[:,1]**2+(X[:,2]*X[:,3])**2,4,1.5),
 ("2sq+1sq+(dmu)^2 =R_local(->2)", lambda X:(X[:,:3]**2).sum(1)+(X[:,3]*X[:,4])**2,5,2.0),
 # with (wy)^2 prefactor, DISTINCT coords, over-origin model: loss=(w y)^2 * R_local
 # BUT with FLAT measure on w,y this is the WRONG measure; use it only to see the product effect:
 ("(wy)^2*(2sq+(dmu)^2) flat", lambda X:(X[:,0]*X[:,1])**2*((X[:,2:4]**2).sum(1)+(X[:,4]*X[:,5])**2),6,None),
]
for name,f,dim,exp in tests:
    r=rlct_mc(f,dim); print(f"  {name:42s} MC rlct = {r:.3f}" + (f"   (expect {exp})" if exp else ""))
