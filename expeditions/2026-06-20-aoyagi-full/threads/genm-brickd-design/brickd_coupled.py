import numpy as np
rng=np.random.default_rng(5)
# After the Γ-shear/D-integral (shell_corankPivot_coupled_le), the RHS integrand (drop pivot weight w=0,
# conservative) is:  det(Q_b Q_b^T)^{-a/2} · frobSq(C·Q_p·Π_{Q_b^perp})^{-e},  e=c'-ab/2.
# Test threshold e* : is the JOINT ∫_z∫_C∫_{A_cor} finite for e < 1/2·minAdm_red = 1.5 (i.e. c'<T2=2.5)?
# u=1,a=1,b=2,n=3,n0=3,Zf=I.  C is a×u=1×1 (scalar). Q_p=z (1×3). Q_b=A_cor (2×3). Π rank-1.
u,a,b,n,n0=1,1,2,3,3
def integrand_batch(e,N):
    z=rng.uniform(-1,1,size=(N,3))            # Q_p rows (1x3)
    C=rng.uniform(-1,1,size=(N,))             # scalar
    Ac=rng.uniform(-1,1,size=(N,2,3))         # Q_b
    Qb=Ac
    G=Qb@np.transpose(Qb,(0,2,1))             # (N,2,2)
    det=np.abs(np.linalg.det(G))
    # projector Π = I - Qb^T (Qb Qb^T)^{-1} Qb  (3x3)
    Ginv=np.linalg.inv(G+1e-15*np.eye(2))
    Proj=np.transpose(Qb,(0,2,1))@Ginv@Qb     # (N,3,3) onto rowspan Qb
    Pperp=np.eye(3)[None]-Proj
    QpPi=np.einsum('ni,nij->nj',z,Pperp)      # Q_p·Π  (N,3)
    resid=(C**2)*(QpPi**2).sum(axis=1)        # frobSq(C·Q_p·Π)
    val=det**(-a/2.0)*np.maximum(resid,1e-300)**(-e)
    return val
vol=2.0**(3+1+6)
def J(e,N): 
    v=integrand_batch(e,N); return v.mean()*vol, np.sort(v)[::-1][:5].sum()/max(v.sum(),1e-300)
print("coupled Schur-residual threshold (w=0, conservative); predicted finite iff e<1.5 (c'<T2=2.5)")
for e in [0.8,1.0,1.2,1.4,1.5,1.6,1.8]:
    v1,_=J(e,150_000); v2,top=J(e,600_000)
    print(f" e={e:4.2f} (c'={e+1:4.2f}): J(1.5e5)={v1:.3e} J(6e5)={v2:.3e} ratio={v2/max(v1,1e-300):5.2f} top5={top:.3f}")
