import numpy as np
rng=np.random.default_rng(7)
def prod_chain(widths, N):
    mats=[rng.uniform(-1,1,(N,widths[i],widths[i+1])) for i in range(len(widths)-1)]
    Y=mats[0]
    for m in mats[1:]:
        Y=np.einsum('nij,njk->nik',Y,m)
    return (Y**2).sum(axis=(1,2))
def rlct_fit(widths,N=60_000_000,label=""):
    f=prod_chain(widths,N)
    epss=np.array([1e-2,3e-3,1e-3,3e-4,1e-4,3e-5,1e-5,3e-6])
    V=np.array([(f<e).mean() for e in epss])
    le=np.log(epss); lv=np.log(V)
    # pure power slope (smallest 4)
    sp=np.polyfit(le[-4:],lv[-4:],1)[0]
    # log-corrected: lv = a + lam*le + (m-1)*log(-le)   (since log(1/eps)=-le)
    X=np.column_stack([np.ones_like(le), le, np.log(-le)])
    coef,*_=np.linalg.lstsq(X,lv,rcond=None)
    lam=coef[1]; mm1=coef[2]
    print(f"{label} widths={widths}: pure-slope(sm4)={sp:.3f} | logfit lambda={lam:.3f} (m-1={mm1:.2f}) | V(1e-5)={V[-2]:.2e}")
    return sp,lam
print("CALIBRATION (expected lambda=minAdm/2):")
rlct_fit([2,2],label="  (2,2) exp=2.0   ")     # sum of 4 squares -> 2.0
rlct_fit([2,2,2],label="  (2,2,2) exp=1.5 ")   # minAdm=3 -> 1.5
rlct_fit([3,3,3],label="  (3,3,3) exp=3.0 ")   # minAdm=6 -> 3.0? aoyagiLambda(3,3,3)? check below
print("\nTARGET:")
rlct_fit([2,2,2,2],label="  (2,2,2,2) exp=1.5")
