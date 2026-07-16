"""
Honest RLCT of a MULTI-LAYER product ||X1 X2 ... XL||^2 over 0 via importance-sampled tail exponent.
Each matrix X_i = r_i * Omega_i, r_i log-uniform in [10^-D,1], Omega_i uniform on unit Frobenius sphere.
Lebesgue measure dX_i = r_i^{dim_i - 1} dr_i dOmega_i ; sampling r_i ~ loguniform (pdf 1/(r ln(10^D))),
reweight by r_i^{dim_i}.  P(loss<t) ~ t^lambda.  Estimate lambda = d log P / d log t (small-t slope).
This importance sampling REACHES tiny loss (product of small radii), unlike uniform MC.
Predicted lambda = minAdm(widths)/2  (paper codim /2, Aoyagi).
"""
import numpy as np
from functools import lru_cache

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    m0,m1=M[0],M[1]; rest=M[2:]
    return min((m0-t)*(m1-t)+minAdm((t,)+rest) for t in range(0,min(m0,m1)+1))

def rlct_tail(dims_chain, N=6000000, D=8, seed=0):
    """dims_chain = widths (w0,w1,...,wL); matrices X_i are w_i x w_{i+1}."""
    rng=np.random.default_rng(seed)
    shapes=[(dims_chain[i],dims_chain[i+1]) for i in range(len(dims_chain)-1)]
    dimsz=[a*b for (a,b) in shapes]
    logw=np.zeros(N)      # log importance weight
    mats=[]
    for (sh,dz) in zip(shapes,dimsz):
        G=rng.standard_normal((N,)+sh)
        fro=np.sqrt((G**2).sum(axis=(1,2),keepdims=True))
        Omega=G/fro                                   # uniform on unit Frobenius sphere
        lr=rng.uniform(-D*np.log(10),0.0,size=N)      # log r, uniform
        r=np.exp(lr)
        X=Omega*r[:,None,None]
        mats.append(X)
        # reweight: target Lebesgue on unit ball ~ dX ; sampling density in r is loguniform
        # dX = r^{dz-1} dr dOmega ; loguniform pdf(r) = 1/(r * D ln10). weight ∝ r^{dz-1}/(pdf) = r^{dz}*(D ln10)
        logw += dz*lr
    # product
    P=mats[0]
    for X in mats[1:]:
        P=np.einsum('nij,njk->nik',P,X)
    loss=(P**2).sum(axis=(1,2))
    w=np.exp(logw-logw.max())   # normalized-ish weights (constant factors cancel in slope)
    # weighted P(loss<t)
    ts=np.array([1e-2,3e-3,1e-3,3e-4,1e-4,3e-5,1e-5,3e-6,1e-6])
    logt=[]; logP=[]
    Wtot=w.sum()
    for t in ts:
        m=loss<t
        Pt=w[m].sum()/Wtot
        if Pt>0:
            logt.append(np.log(t)); logP.append(np.log(Pt))
    logt=np.array(logt); logP=np.array(logP)
    A=np.vstack([logt,np.ones_like(logt)]).T
    slope,_=np.linalg.lstsq(A,logP,rcond=None)[0]
    return slope, list(zip([f"{np.exp(x):.0e}" for x in logt],[round(np.exp(y),5) for y in logP]))

for chain,label in [((2,2,2,2),"u=2,deep=(2,2,2) [3-layer product]"),
                    ((2,2,2),"u=2,deep=(2,2) [2-layer, RRR]"),
                    ((3,4,4),"u=3,deep=(4,4) [(4,4,4,4)@u3 full collapse]"),
                    ((2,3,2,3),"u=2,deep=(3,2,3)")]:
    lam=minAdm(chain)/2
    slope,tab=rlct_tail(chain)
    print(f"{label}: predicted lambda=minAdm{chain}/2={minAdm(chain)}/2={lam}")
    print(f"    measured tail lambda ~ {slope:.3f}   (codim ~ {2*slope:.2f} vs minAdm={minAdm(chain)})")
    print(f"    P(loss<t):",tab)
