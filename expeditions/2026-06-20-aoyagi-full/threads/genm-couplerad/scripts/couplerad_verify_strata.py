import numpy as np
rng=np.random.default_rng(3)
def frob2(X): return float(np.sum(X*X))
# Codex decoupling: ||P Q + B Qb||^2 = ||P (Q Pi)||^2 + ||Btil Qb||^2, Btil=B+P Az, Az=Q Qb^T (Qb Qb^T)^-1
def check_decouple(u,a,b,n):
    Q=rng.standard_normal((u,n)); Qb=rng.standard_normal((b,n))
    G=Qb@Qb.T; Pi=np.eye(n)-Qb.T@np.linalg.inv(G)@Qb; Az=Q@Qb.T@np.linalg.inv(G)
    P=rng.standard_normal((u,u)); B=rng.standard_normal((u,b))
    lhs=frob2(P@Q+B@Qb); Bt=B+P@Az; rhs=frob2(P@(Q@Pi))+frob2(Bt@Qb)
    return abs(lhs-rhs)
print("Codex decoupling ||PQ+BQb||^2 = ||P(QPi)||^2+||Btil Qb||^2:")
for (u,a,b,n) in [(3,1,1,4),(2,2,3,6),(4,2,1,5)]:
    print(f"  u{u}a{a}b{b}n{n}: err={check_decouple(u,a,b,n):.2e}")

# corank-l pole: build z0 so QPi=z0 ZPi has rank u-l; measure k = #eigenvalues of H ~ delta^2; check k=l(u+a)
def eig_H(u,a,b,Z,Ac,Pi,z0):
    Qinl=z0@Z; Qb=Ac@Z
    Gs=np.vstack([Qinl,Qb])@np.vstack([Qinl,Qb]).T; KK=Qinl@Pi@Qinl.T
    return np.array(sorted(list(np.linalg.eigvalsh(Gs))*u+list(np.linalg.eigvalsh(KK))*a))
def setup(u,a,b,M2,n,rho_d,seed=0):
    r=np.random.default_rng(seed)
    Z=np.linalg.qr(r.standard_normal((M2,M2)))[0][:,:rho_d]@r.standard_normal((rho_d,n))
    Ac=r.standard_normal((b,M2)); Qb=Ac@Z; Pi=np.eye(n)-Qb.T@np.linalg.pinv(Qb@Qb.T)@Qb
    return Z,Ac,Pi
print("\ncorank-l of QPi: measure k (claim l(u+a)); pick d>=a+2 cell")
# want d=rho_d-b >= a+2. take u=2,a=1,b=1,rho_d=6 => d=5>=3. M2=6,n=7
u,a,b,M2,n,rho_d=2,1,1,6,7,6; d=rho_d-b
Z,Ac,Pi=setup(u,a,b,M2,n,rho_d)
ZPi=Z@Pi
# basis of rowspace(ZPi): d-dim in M2
Ub=np.linalg.qr(ZPi.T)[0][:, :np.linalg.matrix_rank(ZPi,1e-8)]
def z0_corank(ell,delta,seed):
    r=np.random.default_rng(seed)
    # z0 in ZPi-coords (u x d), make ell singular values ~delta
    A=r.standard_normal((u,d)); Usv,s,Vt=np.linalg.svd(A,full_matrices=False)
    s[:ell]*=delta                       # shrink ell singular values
    Aeff=(Usv*s)@Vt
    comp = r.standard_normal((u,M2-d)) if M2>d else np.zeros((u,0))
    Ucomp=np.linalg.qr(np.eye(M2)-Ub@Ub.T)[0][:,:M2-d] if M2>d else np.zeros((M2,0))
    return Aeff@Ub.T + comp@Ucomp.T
rho0=(u+a)*min(u,d)+u*b
print(f"  u={u} a={a} b={b} d={d} rho0(formula (u+a)min(u,d)+ub)={rho0}")
for ell in range(1,u+1):
    ea=eig_H(u,a,b,Z,Ac,Pi,z0_corank(ell,1e-3,11)); eb=eig_H(u,a,b,Z,Ac,Pi,z0_corank(ell,1e-4,11))
    ea=np.array(sorted(ea)); eb=np.array(sorted(eb)); nz=ea>1e-13*ea.max()
    p=np.log10(np.maximum(ea[nz],1e-300)/np.maximum(eb[nz],1e-300)); k=int(np.sum(p>1.5))
    cl=ell*(abs(u-d)+ell); phi=rho0-ell*(u+a)+cl
    print(f"  ell={ell}: k_meas={k} claim l(u+a)={ell*(u+a)} c_l={cl} phi={phi}")
