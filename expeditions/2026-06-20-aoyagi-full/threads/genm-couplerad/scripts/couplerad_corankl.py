import numpy as np
def eig_H(u,a,b,Z,Ac,Pi,z0):
    Qinl=z0@Z; Qb=Ac@Z
    Gs=np.vstack([Qinl,Qb])@np.vstack([Qinl,Qb]).T; KK=Qinl@Pi@Qinl.T
    return np.array(sorted(list(np.linalg.eigvalsh(Gs))*u+list(np.linalg.eigvalsh(KK))*a))
def setup(u,a,b,M2,n,rho_d,seed=0):
    r=np.random.default_rng(seed)
    Z=np.linalg.qr(r.standard_normal((M2,M2)))[0][:,:rho_d]@r.standard_normal((rho_d,n))
    Ac=r.standard_normal((b,M2)); Qb=Ac@Z; Pi=np.eye(n)-Qb.T@np.linalg.pinv(Qb@Qb.T)@Qb
    return Z,Ac,Pi
# d>=a+2 cell: u=2,a=1,b=1,rho_d=6,M2=6,n=7 => d=rho_d-b=5
u,a,b,M2,n,rho_d=2,1,1,6,7,6; d=rho_d-b
Z,Ac,Pi=setup(u,a,b,M2,n,rho_d); ZPi=Z@Pi                       # M2 x n
Ucol=np.linalg.qr(ZPi)[0][:, :np.linalg.matrix_rank(ZPi,1e-8)]   # M2 x d colspace(ZPi)
dd=Ucol.shape[1]
Ucomp=np.linalg.qr(np.eye(M2)-Ucol@Ucol.T)[0][:, :M2-dd]         # M2 x (M2-d)
def z0_corank(ell,delta,seed):
    r=np.random.default_rng(seed)
    A=r.standard_normal((u,dd)); U,s,Vt=np.linalg.svd(A,full_matrices=False); s[:ell]*=delta
    Aeff=(U*s)@Vt
    comp=r.standard_normal((u,M2-dd)) if M2>dd else np.zeros((u,0))
    return Aeff@Ucol.T + (comp@Ucomp.T if M2>dd else 0)
rho0=(u+a)*min(u,d)+u*b
print(f"d>=a+2 cell: u={u} a={a} b={b} d={d} rho0={rho0} (min(u,d)={min(u,d)})")
for ell in range(1,u+1):
    ea=eig_H(u,a,b,Z,Ac,Pi,z0_corank(ell,1e-3,11)); eb=eig_H(u,a,b,Z,Ac,Pi,z0_corank(ell,1e-4,11))
    ea=np.array(sorted(ea)); eb=np.array(sorted(eb)); nz=ea>1e-12*ea.max()
    p=np.log10(np.maximum(ea[nz],1e-300)/np.maximum(eb[nz],1e-300)); k=int(np.sum(p>1.5))
    cl=ell*(abs(u-d)+ell); phi=rho0-ell*(u+a)+cl
    print(f"  ell={ell}: k_meas={k} claim l(u+a)={ell*(u+a)} match={k==ell*(u+a)}  c_l=l(|u-d|+l)={cl}  phi={phi}")
# min_l phi and form A comparison
phis=[rho0]+[rho0-l*(u+a)+l*(abs(u-d)+l) for l in range(1,min(u,d)+1)]
print(f"  phi(0..)={phis}  min={min(phis)}  formA phi(u)=u*rho_d={u*rho_d}  intermediate tighter={min(phis)<u*rho_d}")
