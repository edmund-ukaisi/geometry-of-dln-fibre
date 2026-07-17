"""
Part 5b -- is the (fixed-F rlct=3) vs (chart-varying-F rlct~2.6) gap a CONDITIONING bias or a real effect?
If tightening the dominant-minor chart (|det lead| >= tau, larger tau => F better conditioned, sigma_min(F)
bounded further from 0) pushes the chart rlct toward 3, the gap is finite-eps conditioning bias and the
single-factor prediction (rlct=3, F contributes no rank-drop singularity) holds. Also compute the EXACT
theoretical rlct of ||F.A1||^2 on the full-rank locus.
"""
import numpy as np
rng = np.random.default_rng(11)

def slope(fvals, eps, lo=1e-3, hi=6e-2):
    fr=np.array([np.mean(fvals<e) for e in eps]); lg=np.log(eps); lv=np.log(np.maximum(fr,1e-12))
    m=(fr>lo)&(fr<hi)
    if m.sum()<3: m=(fr>3e-4)&(fr<1.2e-1)
    A=np.vstack([lg[m],np.ones(m.sum())]).T
    s,_=np.linalg.lstsq(A,lv[m],rcond=None)[0]; return s
eps=np.exp(np.linspace(np.log(3e-7),np.log(1e-1),26))
M0,M1,M2=2,3,3
NBASE=9_000_000
print("Tightening the dominant-minor chart |det(leading 2x2)| >= tau:")
for tau in [0.05, 0.15, 0.30, 0.50, 0.80]:
    F=rng.uniform(-1,1,size=(NBASE,M0,M1))
    lead=F[:,:,:M0]; dl=lead[:,0,0]*lead[:,1,1]-lead[:,0,1]*lead[:,1,0]
    F=F[np.abs(dl)>=tau]
    A1=rng.uniform(-1,1,size=(F.shape[0],M1,M2))
    W=np.einsum('nij,njk->nik',F,A1); f=np.sum(W**2,axis=(1,2))
    # also record sigma_min(F) distribution
    smin=np.linalg.svd(F,compute_uv=False)[:,-1]
    print(f"  tau={tau:.2f}: chart rlct slope ~ {slope(f,eps):.3f}   (n={F.shape[0]:>8d}, median sigma_min(F)={np.median(smin):.3f})")
print()
print("EXACT theory: on the full-rank chart, {F.A1=0} <=> colspace(A1) subset ker F (dim M1-M0=1).")
print("Transverse contact is QUADRATIC (||F.A1||^2 = ||F.E||^2, sigma_min(F)>0), codim = M0*M2 - 0? ->")
print("dim{A1:F.A1=0}=M1*M2 - M0*M2 = (M1-M0)*M2 = 1*3 = 3; codim=6; quadratic => rlct = 6/2 = 3.")
print("=> single-factor prediction rlct=3; chart slope should climb toward 3 as tau grows.")
