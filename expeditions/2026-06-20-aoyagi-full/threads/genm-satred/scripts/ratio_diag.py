"""
satred: the decisive diagnostic.

Honest saturated front-charge integral (arity-4 parent M=(M0,M1,M2,M3), a=0, u=M0<=M1):
   I(c') = ∫ frobSq( (P z0 + B12 A_cor) · z1 )^{-c'} d(P,z0,B12,A_cor,z1)
           over [-1,1] boxes, P also required invertible (measure-1 constraint, MC ignores nullset)
Reduced-chain box integral (target RMBTF(redChain u M) = RMBTF(u,M2,M3)) at matching radius T*:
   R_T(c') = ∫ frobSq( zt0 · z1 )^{-c'} d(zt0,z1),  zt0 in [-T*,T*]^{uxM2}, z1 in [-1,1]^{M2xM3}
where T* = u + b (sup of ||P z0 + B12 A_cor||_inf).

Claim under test: I(c') <= K * R_{T*}(c') with K FINITE and STABLE as c'->threshold.
 - ratio bounded & stable  => bounded pushforward density => CLEAN route (iii), K = ||rho||_inf.
 - ratio DIVERGES as c'->thr => extra singularity from front block; needs eps-headroom or route (i).

MC estimate of a singular integral: for c' below threshold the mean converges; we watch the
RATIO r(c') = I(c')/R_{T*}(c') as c' climbs to threshold. Report with jackknife-ish repeats.
"""
import numpy as np

def frobSq_prod(zt0, z1):
    # zt0: (...,u,M2), z1: (...,M2,M3) -> ||zt0 z1||_F^2
    P = np.einsum('...ij,...jk->...ik', zt0, z1)
    return (P**2).sum(axis=(-1,-2))

def honest_I(u,M2,M3,b,cp,N,rng):
    P  = rng.uniform(-1,1,(N,u,u))
    z0 = rng.uniform(-1,1,(N,u,M2))
    B12= rng.uniform(-1,1,(N,u,b))
    Ac = rng.uniform(-1,1,(N,b,M2))
    z1 = rng.uniform(-1,1,(N,M2,M3))
    zt0 = np.einsum('nij,njk->nik',P,z0) + np.einsum('nij,njk->nik',B12,Ac)
    f = frobSq_prod(zt0,z1)
    g = f**(-cp)
    vol = (2.0)**(u*u+u*M2+u*b+b*M2+M2*M3)  # lebesgue vol of the box product
    return g.mean()*vol, g

def reduced_R(u,M2,M3,Tstar,cp,N,rng):
    zt0 = rng.uniform(-Tstar,Tstar,(N,u,M2))
    z1  = rng.uniform(-1,1,(N,M2,M3))
    f = frobSq_prod(zt0,z1)
    g = f**(-cp)
    vol = (2*Tstar)**(u*M2) * (2.0)**(M2*M3)
    return g.mean()*vol, g

cases = [
    ("TALL  u=2>M2=1  M=(2,3,1,1)", 2,1,1,1, 1),   # thr = minAdm(2,1,1)/2 = 0.5
    ("WIDE  u=1<M2=2  M=(1,2,2,2)", 1,2,2,1, 2),   # thr = minAdm(1,2,2)/2 = 1.0
    ("SQ    u=M2=2    M=(2,3,2,2)", 2,2,2,1, 3),   # thr = minAdm(2,2,2)/2 = 1.5
]
N = 2_000_000
for (label,u,M2,M3,b,minAdmRed) in cases:
    thr = minAdmRed/2.0
    Tstar = u+b
    print(f"\n=== {label} : reduced minAdm={minAdmRed}, threshold c'<{thr}, T*={Tstar} ===")
    print(f"{'c/thr':>6} {'c':>7} {'I(c)':>12} {'R_T*(c)':>12} {'ratio I/R':>12}")
    for frac in [0.5,0.7,0.85,0.93,0.97]:
        cp = frac*thr
        rats=[]; Is=[]; Rs=[]
        for seed in range(6):
            rng = np.random.default_rng(1000*seed+hash(label)%997)
            I,_ = honest_I(u,M2,M3,b,cp,N,rng)
            R,_ = reduced_R(u,M2,M3,Tstar,cp,N,rng)
            rats.append(I/R); Is.append(I); Rs.append(R)
        rats=np.array(rats)
        print(f"{frac:>6.2f} {cp:>7.4f} {np.mean(Is):>12.4f} {np.mean(Rs):>12.4f} "
              f"{np.mean(rats):>9.4f}±{np.std(rats):.4f}")
