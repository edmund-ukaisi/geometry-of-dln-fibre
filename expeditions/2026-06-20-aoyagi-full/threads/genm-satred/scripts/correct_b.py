"""
satred CORRECTED: use the RIGHT corank width b = M1 - u  (u = M0 at saturation a=0).
Then u+b = M1, so the front layer X := [P | B12] is M0 x M1 (the FULL first layer) and
Y := [z0 ; A_cor] is M1 x M2 (the FULL second layer), and
    z_tilde0 = X*Y = [P|B12][z0;A_cor]   (M0 x M2)  = the leading layer of redChain u M.
Codex reframing: z_tilde0 = X Y, a product of two independent random matrices, X of full row
rank M0 (since P invertible => [P|B12] full row rank M0, uniformly, even as det P -> 0, because
the B12 block supplements the near-singular P). So the map Y |-> X Y is a bounded-density
SURJECTION and the pushforward density rho_XY(z_tilde0) should be BOUNDED -> clean reduction,
det-P hazard evaporates.

Tests:
 (A) density of z_tilde0 = X Y near 0: bounded (stabilises) as eps->0?
 (B) RLCT lambda_H of the honest saturated integral = 1/2 minAdm(M) (no drop)?
 (C) contrast: does det P -> 0 concentrate the density? measure density conditioned on |det P|<0.05.
"""
import numpy as np
rng = np.random.default_rng(3)

def sample_ztilde(M0,M1,M2,N, require_P_unit=True):
    # X = [P | B12], P = M0xM0 invertible, B12 = M0x(M1-M0); Y = M1 x M2
    b = M1 - M0
    P  = rng.uniform(-1,1,(N,M0,M0))
    B12= rng.uniform(-1,1,(N,M0,b)) if b>0 else np.zeros((N,M0,0))
    X  = np.concatenate([P,B12],axis=2)              # (N,M0,M1)
    Y  = rng.uniform(-1,1,(N,M1,M2))
    Z  = np.einsum('nij,njk->nik',X,Y)               # (N,M0,M2)
    detP = np.linalg.det(P)
    return Z, detP

def density_at0(Z, eps):
    d = Z.reshape(len(Z),-1)
    inb = np.all(np.abs(d)<=eps,axis=1)
    return inb.mean()/(2*eps)**d.shape[1], inb.sum()

print("=== (A) density of z~0 = [P|B12][z0;A_cor] near 0 (correct b=M1-u) ===")
for (M0,M1,M2,lab) in [(1,3,3,"(1,3,3,3) u=1,b=2"),(1,2,2,"(1,2,2,2) u=1,b=1"),
                       (2,3,2,"(2,3,2,2) u=2,b=1"),(1,4,4,"(1,4,4,4) u=1,b=3"),
                       (2,4,3,"(2,4,3,3) u=2,b=2")]:
    N=5_000_000
    Z,_ = sample_ztilde(M0,M1,M2,N)
    row=[]
    for eps in [0.2,0.1,0.05,0.025]:
        dv,cnt=density_at0(Z,eps); row.append(f"eps={eps}: rho~{dv:7.3f}(n={cnt})")
    print(f"  [{lab}] dim={M0*M2}: "+" | ".join(row))

print("\n=== (C) does det P->0 concentrate the density? (compare rho at 0 | |detP|<0.05 vs all) ===")
for (M0,M1,M2,lab) in [(1,3,3,"(1,3,3,3)"),(2,3,2,"(2,3,2,2)"),(1,4,4,"(1,4,4,4)")]:
    N=6_000_000
    Z,detP = sample_ztilde(M0,M1,M2,N)
    eps=0.1
    d=Z.reshape(len(Z),-1); inb=np.all(np.abs(d)<=eps,axis=1)
    small=np.abs(detP)<0.05
    # density near 0 conditioned on small det P (per unit small-detP measure):
    rho_all = inb.mean()/(2*eps)**d.shape[1]
    rho_small = (inb&small).sum()/max(small.sum(),1)/(2*eps)**d.shape[1]
    print(f"  [{lab}] rho@0(all)={rho_all:.3f}  rho@0(|detP|<0.05, per-unit)={rho_small:.3f}  "
          f"frac small={small.mean():.3f}")

print("\n=== (B) RLCT lambda_H (honest saturated) via sublevel-volume slope, correct b ===")
def F_honest(M0,M1,M2,M3,N):
    Z,_ = sample_ztilde(M0,M1,M2,N)
    z1 = rng.uniform(-1,1,(N,M2,M3))
    Pr = np.einsum('nij,njk->nik',Z,z1)
    return (Pr**2).sum((-1,-2))
ts=np.array([3e-2,1e-2,3e-3,1e-3,3e-4,1e-4])
def slope(F):
    V=np.array([(F<t).mean() for t in ts]); return np.diff(np.log(np.clip(V,1e-12,None)))/np.diff(np.log(ts))
for (M0,M1,M2,M3,minAdmM,lab) in [(1,3,3,3,3,"(1,3,3,3) need 1.5"),
                                   (2,3,2,2,3,"(2,3,2,2) need 1.5"),
                                   (1,4,4,4,4,"(1,4,4,4) need 2.0")]:
    F=F_honest(M0,M1,M2,M3,7_000_000); sl=slope(F)
    print(f"  [{lab}] lambda_H~{sl[-1]:.3f}  (target 1/2 minAdm(M)={minAdmM/2})  full:{np.array2string(sl,precision=2)}")
