import numpy as np
rng=np.random.default_rng(0)
# Multiplier at EXACT rank-drop of the shared deeper factor B.
# B: M2 x M3, given rank rho (rho nonzero singular values =1, rest =0).
# Predicted: effective spectator dim = (M1-t)*rho ; bounded/log iff a <= (M1-t)*rho, else power g^{-(a-(M1-t)rho)}.
def M_rankB(a, nrows, M2, rho, g, N=3_000_000):
    Y=rng.uniform(-1,1,(N,nrows,M2))
    sig=np.array([1.0]*rho+[0.0]*(M2-rho))      # B singular values (rank rho)
    YB=Y*sig[None,None,:]                        # ||YB||^2 sees only rank-rho part
    n2=(YB**2).sum((1,2))
    return ((g*g+n2)**(-a/2.0)).mean()*(2.0**(nrows*M2))
def slope(gs,Ms): return np.polyfit(np.log(1/gs),np.log(np.maximum(Ms,1e-300)),1)[0]
gs=np.array([1e-1,1e-2,1e-3,1e-4,1e-5])

print("Multiplier at EXACT rank-rho shared factor B. slope 0=>log(reduces); slope>0=>POWER g^{-(a-(M1-t)rho)} (joint).")
print("Predicted power exponent p = max(0, a-(M1-t)*rho).\n")
cases=[
 ("(2,2,2,2) t=1", 1, 1, 2),   # a, nrows=M1-t, M2
 ("(3,3,3,3) t=2", 1, 1, 3),
 ("(4,4,4,4) t=2", 4, 2, 4),
 ("(4,4,4,4) t=3", 1, 1, 4),
]
for name,a,nr,M2 in cases:
    print(f"{name}: a={a}, spectator {nr}x{M2}")
    for rho in range(M2,0,-1):
        Ms=np.array([M_rankB(a,nr,M2,rho,g) for g in gs])
        s=slope(gs,Ms); pred=max(0,a-nr*rho)
        tag = "LOG/bounded (reduces)" if pred==0 else f"POWER g^-{pred} (JOINT needed)"
        print(f"    rank(B)={rho}: eff.dim={nr*rho}, slope={s:+.2f}  pred p={pred}  {tag}")
