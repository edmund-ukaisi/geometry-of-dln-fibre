import numpy as np
rng=np.random.default_rng(11)
# Faithful coupled RHS of shell_corankPivot_coupled_le WITH pivot weight w>0:
#   det(Q_b Q_b^T)^{-a/2} · ( w + frobSq(C·Q_p·Π_{Q_b^perp}) )^{-e},  e=c'-ab/2,
#   w = pivot energy = frobSq(P·Q_p) = P²‖z‖²  (P scalar 1x1 pivot, integrated -> reduced comparator).
# Integrate over z(3),C(1),P(1),A_cor(6). Threshold?  predicted c'<T2=2.5 i.e. e<1.5.
u,a,b,n,n0=1,1,2,3,3
def integ(e,N):
    z=rng.uniform(-1,1,size=(N,3)); C=rng.uniform(-1,1,size=(N,)); P=rng.uniform(-1,1,size=(N,))
    Ac=rng.uniform(-1,1,size=(N,2,3)); Qb=Ac
    G=Qb@np.transpose(Qb,(0,2,1)); det=np.abs(np.linalg.det(G))
    Ginv=np.linalg.inv(G+1e-14*np.eye(2))
    Pproj=np.transpose(Qb,(0,2,1))@Ginv@Qb; Pperp=np.eye(3)[None]-Pproj
    QpPi=np.einsum('ni,nij->nj',z,Pperp); resid=(C**2)*(QpPi**2).sum(axis=1)
    w=(P**2)*(z**2).sum(axis=1)
    val=det**(-a/2.0)*np.maximum(w+resid,1e-300)**(-e)
    return val
vol=2.0**(3+1+1+6)
def J(e,N): v=integ(e,N); return v.mean()*vol, np.sort(v)[::-1][:5].sum()/max(v.sum(),1e-300)
print("coupled RHS WITH pivot weight w=P²‖z‖²; predicted finite iff e<1.5 (c'<T2=2.5)")
for e in [1.0,1.2,1.4,1.5,1.6,1.8,2.0]:
    v1,_=J(e,300_000); v2,top=J(e,1_200_000)
    print(f" e={e:4.2f} (c'={e+1:4.2f}): J(3e5)={v1:.3e} J(1.2e6)={v2:.3e} ratio={v2/max(v1,1e-300):6.2f} top5={top:.3f}")
