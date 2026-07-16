import numpy as np
def eig_H(u,a,b,Z,Ac,Pi,z0):
    Qinl=z0@Z; Qb=Ac@Z
    Gs=np.vstack([Qinl,Qb])@np.vstack([Qinl,Qb]).T; KK=Qinl@Pi@Qinl.T
    return np.array(sorted(list(np.linalg.eigvalsh(Gs))*u+list(np.linalg.eigvalsh(KK))*a))
def setup(u,a,b,M2,n,rho_d,seed=0):
    rng=np.random.default_rng(seed)
    Z=np.linalg.qr(rng.standard_normal((M2,M2)))[0][:,:rho_d]@rng.standard_normal((rho_d,n))
    Ac=rng.standard_normal((b,M2)); Qb=Ac@Z; Pi=np.eye(n)-Qb.T@np.linalg.pinv(Qb@Qb.T)@Qb
    return Z,Ac,Pi,rng
def pole(u,a,b,M2,n,rho_d,q,g,Z,Ac,Pi):
    eb=eig_H(u,a,b,Z,Ac,Pi,g); rho=int(np.sum(eb>1e-9*eb.max()))
    d=1e-3; ea=eig_H(u,a,b,Z,Ac,Pi,d*g); ec=eig_H(u,a,b,Z,Ac,Pi,(d/10)*g)
    ea=np.array(sorted(ea)); ec=np.array(sorted(ec)); nz=ea>1e-13*ea.max()
    p=np.log10(np.maximum(ea[nz],1e-300)/np.maximum(ec[nz],1e-300))
    return 2*q-rho+int(np.sum(p>1.5))

print("=== pole for full-rank vs rank-deficient z0-directions g (radial degeneration z0=delta*g) ===")
print("   need: full-rank g gives the max pole (=2q-ub); rank-deficient dirs give pole <= that (angular integrable)")
for (u,a,b,M2,n,rho_d,cp,tag) in [(3,1,1,4,4,4,4.9,"(4,4,4,4)@u3"),(3,2,1,5,6,5,6.0,"u3a2b1"),(2,2,2,5,5,5,5.0,"a2b2")]:
    q=cp-a*b/2; Z,Ac,Pi,rng=setup(u,a,b,M2,n,rho_d)
    pfull=2*q-u*b
    poles={}
    for r in range(1,u+1):   # z0 = rank-r direction
        ps=[]
        for _ in range(6):
            g=np.random.randn(u,r)@np.random.randn(r,M2)
            ps.append(pole(u,a,b,M2,n,rho_d,q,g,Z,Ac,Pi))
        poles[r]=max(ps)
    print(f"  {tag:12} 2q-ub(full)={pfull:.2f} dimz={u*M2} | pole by rank(g): {poles}  max={max(poles.values()):.2f}  all<=full+eps={max(poles.values())<=pfull+1e-6}")
