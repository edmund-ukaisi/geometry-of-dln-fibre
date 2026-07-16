import numpy as np, itertools
def eig_H(u,a,b,Z,Ac,Pi, z0):
    Qinl=z0@Z; Qb=Ac@Z
    Gs=np.vstack([Qinl,Qb])@np.vstack([Qinl,Qb]).T
    KK=Qinl@Pi@Qinl.T
    return np.array(sorted(list(np.linalg.eigvalsh(Gs))*u + list(np.linalg.eigvalsh(KK))*a))
def setup(u,a,b,M2,n,rho_d,seed=0):
    rng=np.random.default_rng(seed)
    Z=np.linalg.qr(rng.standard_normal((M2,M2)))[0][:,:rho_d]@rng.standard_normal((rho_d,n))
    Ac=rng.standard_normal((b,M2)); Qb=Ac@Z
    Pi=np.eye(Z.shape[1])-Qb.T@np.linalg.pinv(Qb@Qb.T)@Qb
    return Z,Ac,Pi,rng
def pole_full(u,a,b,M2,n,rho_d,q,seed=0):
    Z,Ac,Pi,rng=setup(u,a,b,M2,n,rho_d,seed); g=rng.standard_normal((u,M2))
    ebig=eig_H(u,a,b,Z,Ac,Pi,g); rho=int(np.sum(ebig>1e-9*ebig.max()))
    d=1e-3; ea=eig_H(u,a,b,Z,Ac,Pi,d*g); eb=eig_H(u,a,b,Z,Ac,Pi,(d/10)*g)
    ea=np.array(sorted(ea)); eb=np.array(sorted(eb)); m=ea.max()
    nz=ea>1e-13*m
    p=np.log10(np.maximum(ea[nz],1e-300)/np.maximum(eb[nz],1e-300))  # scaling exponent p: eig~delta^p
    k=int(np.sum(p>1.5))   # delta^2 dirs (p~2)
    return rho,k,2*q-rho+k,sorted(np.round(p,2).tolist())

print("pole(full z0->0) = 2q-rho+k  vs 2q-ub ; dimz=uM2")
for (u,a,b,M2,n,rho_d,cp,tag) in [
    (3,1,1,4,4,4,4.9,"(4,4,4,4)@u3"),(2,1,2,5,4,4,4.9,"(3,4,5,4)@u2"),
    (2,2,2,5,5,5,5.0,"a2b2"),(3,2,1,5,6,5,6.0,"u3a2b1"),(2,2,3,6,5,5,5.0,"b3")]:
    q=cp-a*b/2; rho,k,pole,ps=pole_full(u,a,b,M2,n,rho_d,q)
    print(f" {tag:14} 2q={2*q:.1f} rho={rho} k={k} pole={pole:.2f} 2q-ub={2*q-u*b:.2f} match={abs(pole-(2*q-u*b))<1e-6} dimz={u*M2} ok={pole<u*M2}")
