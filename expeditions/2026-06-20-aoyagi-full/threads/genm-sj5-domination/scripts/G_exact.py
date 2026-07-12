import numpy as np
from scipy import integrate
from scipy.special import gamma

# TRUE inner structure at the anchor (3,3,2,2): a=1,b=1,M2=2, tail A3 = diag(1, sg).
# Freed corner Gamma in R^{a*b}=R^1.  A_cor in R^{M2}=R^2 (=(p,q)).
# tau = ||A_cor A3|| = sqrt(p^2 + sg^2 q^2).   (b=1)
# Freed-corner integral (exact, with residual constant c0):
#   I(w,tau) = ∫_{Gamma in [-T,T]} (w + (c0 + Gamma*tau)^2)^{-cp} dGamma      [ab=1]
# G(w,sg) = ∫_{A_cor in [-1,1]^2} I(w, tau(p,q,sg)) dp dq.
# Compare G's dependence on (w, sg) to decide Way1 (G~sg^{-1} w^{-(cp-1/2)}) vs Way2 (G~log).

T=1.0
def Igamma(w, tau, cp, c0=0.3, Ng=4001):
    g=np.linspace(-T,T,Ng)
    val=(w+(c0+g*tau)**2)**(-cp)
    return np.trapezoid(val,g)

def G(w,sg,cp,Np=401):
    p=np.linspace(-1,1,Np); q=np.linspace(-1,1,Np)
    P,Q=np.meshgrid(p,q,indexing='ij')
    tau=np.sqrt(P**2+sg**2*Q**2)
    # vectorize Igamma over grid via analytic-ish: do coarse loop
    out=np.zeros_like(tau)
    # cheaper: sample fewer gamma points but exact enough
    g=np.linspace(-T,T,801)
    for iidx in range(tau.shape[0]):
        tt=tau[iidx]           # 1D array length Np
        # integrand over g for each tt: shape (Np, 801)
        arr=(w+(0.3+np.outer(tt,g))**2)**(-cp)
        out[iidx]=np.trapezoid(arr,g,axis=1)
    return np.trapezoid(np.trapezoid(out,q,axis=1),p)

print("Anchor a=1,b=1,M2=2. Fit G(w,sg) exponents. cp=c' varies.")
print("Way1 predicts G ~ sg^{-1} * w^{-(cp-1/2)} ; Way2 predicts corank weight ~ log(1/sg), G ~ (log) * w^{-(cp-1/2)}")
print()
for cp in [1.2, 1.5, 1.8]:
    print(f"--- c'={cp} (e=cp-0.5={cp-0.5}) ---")
    # sg dependence at fixed moderate w
    for w in [1e-2]:
        sgs=np.array([1e-1,1e-2,1e-3,1e-4])
        Gs=np.array([G(w,sg,cp) for sg in sgs])
        sl=np.diff(np.log(Gs))/np.diff(np.log(sgs))
        print(f"  w={w}: G(sg)= {np.array2string(Gs,precision=4)}  d logG/d log sg = {np.array2string(sl,precision=3)}  (Way1=>-1, Way2=>0/log)")
    # w dependence at fixed small sg
    for sg in [1e-3]:
        ws=np.array([1e-1,1e-2,1e-3,1e-4])
        Gs=np.array([G(w,sg,cp) for w in ws])
        sl=np.diff(np.log(Gs))/np.diff(np.log(ws))
        print(f"  sg={sg}: G(w)= {np.array2string(Gs,precision=4)}  d logG/d log w = {np.array2string(sl,precision=3)}  (expect -(cp-1/2)={-(cp-0.5)})")
