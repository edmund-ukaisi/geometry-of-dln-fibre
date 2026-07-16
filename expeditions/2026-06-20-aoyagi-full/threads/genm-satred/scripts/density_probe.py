"""
satred: probe the pushforward density rho(z_tilde0) of the front block
    z_tilde0 = P*z0 + B12*A_cor      (u x M2 matrix)
where P (uxu, invertible-in-box), z0 (u x M2), B12 (u x b), A_cor (b x M2)
are uniform on [-1,1] entrywise boxes.

Question: is rho BOUNDED (clean route iii/ii domination I <= K*RMBTF), or
singular at z_tilde0 low-rank?  We estimate the density near a target W by
counting samples that land in a small L-inf ball of radius eps around W and
dividing by the ball volume (uM2-dim), then track how the estimate scales as
eps shrinks (bounded density => estimate stabilizes; singular => grows).

Also: single-product density of X = P*z0 alone -> expected divergent at 0 for
M2>=1 (the |det P|^{-M2} artifact); the SUM with B12*A_cor should tame it.
"""
import numpy as np

rng = np.random.default_rng(0)

def sample_ztilde(u, M2, b, N, include_cross=True, include_pz0=True):
    P  = rng.uniform(-1,1,size=(N,u,u))
    z0 = rng.uniform(-1,1,size=(N,u,M2))
    W = np.zeros((N,u,M2))
    if include_pz0:
        W += np.einsum('nij,njk->nik', P, z0)
    if include_cross and b>0:
        B12   = rng.uniform(-1,1,size=(N,u,b))
        A_cor = rng.uniform(-1,1,size=(N,b,M2))
        W += np.einsum('nij,njk->nik', B12, A_cor)
    return W

def density_at(W, target, eps):
    # fraction of samples in L-inf eps-ball / ball-volume, dims = prod(target.shape)
    d = W - target[None,...]
    inball = np.all(np.abs(d.reshape(len(d),-1)) <= eps, axis=1)
    frac = inball.mean()
    vol = (2*eps)**target.size
    return frac/vol, inball.sum()

print("=== density near W=0, L-inf ball, shrinking eps ===")
print("(bounded density -> stabilises; singular -> grows as eps->0)\n")
for (u,M2,b,label) in [(1,1,1,"scalar u=M2=1"),
                       (2,2,1,"square u=M2=2 (M=(2,3,2,2))"),
                       (1,2,1,"wide u=1<M2=2 (M=(1,2,2,2))"),
                       (2,1,1,"tall u=2>M2=1 (M=(2,3,1,1))"),
                       (2,2,2,"square u=M2=2, b=2"),
                       (3,3,1,"square u=M2=3")]:
    N = 4_000_000
    W = sample_ztilde(u,M2,b,N)
    row=[]
    for eps in [0.3,0.15,0.075,0.0375]:
        dens,cnt = density_at(W, np.zeros((u,M2)), eps)
        row.append(f"eps={eps:.4f}: rho~{dens:8.3f} (n={cnt})")
    print(f"[{label}] dim={u*M2}")
    for r in row: print("    ",r)
    # compare: single product P*z0 alone (no cross term) -> expect blow up
    Wp = sample_ztilde(u,M2,b,N,include_cross=False)
    drow=[]
    for eps in [0.3,0.15,0.075,0.0375]:
        dens,cnt = density_at(Wp, np.zeros((u,M2)), eps)
        drow.append(f"eps={eps:.4f}: rho~{dens:8.3f}")
    print(f"    [P*z0 ALONE, no cross]:")
    for r in drow: print("        ",r)
    print()
