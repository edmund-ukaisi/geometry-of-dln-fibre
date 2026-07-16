"""
satred: measure the finiteness threshold (RLCT lambda) directly via the volume-scaling law
    Vol{ F < t }  ~  C * t^lambda * |log t|^{m-1}     (t -> 0+)
For the loss F = frobSq(prod)^, the integral ∫ F^{-c'} converges iff c' < lambda.  So lambda is
the EXACT finiteness threshold; log factors do not shift it.  We estimate lambda as the local
slope  d log Vol{F<t} / d log t  in the small-t regime, for:
  (H) honest:  F_H = || (P z0 + B12 Acor) z1 ||_F^2   over (P,z0,B12,Acor,z1) boxes, P invertible
  (R) reduced: F_R = || W z1 ||_F^2                    over (W in box_T*, z1 box)
If lambda_H == lambda_R == (1/2)*minAdm(reduced), the front block does NOT lower the RLCT:
reduction is clean at the SAME threshold (log-density is a multiplicity/log effect only).
If lambda_H < that, the threshold genuinely drops (would need catalogued headroom / obstruction).
"""
import numpy as np
rng = np.random.default_rng(7)

def F_honest(u,M2,M3,b,N):
    P  = rng.uniform(-1,1,(N,u,u)); z0 = rng.uniform(-1,1,(N,u,M2))
    B12= rng.uniform(-1,1,(N,u,b)); Ac = rng.uniform(-1,1,(N,b,M2))
    z1 = rng.uniform(-1,1,(N,M2,M3))
    Z = np.einsum('nij,njk->nik',P,z0)+np.einsum('nij,njk->nik',B12,Ac)
    Pr= np.einsum('nij,njk->nik',Z,z1)
    return (Pr**2).sum((-1,-2))

def F_reduced(u,M2,M3,Tstar,N):
    W = rng.uniform(-Tstar,Tstar,(N,u,M2)); z1=rng.uniform(-1,1,(N,M2,M3))
    Pr= np.einsum('nij,njk->nik',W,z1)
    return (Pr**2).sum((-1,-2))

def slope_lambda(F, ts):
    # Vol{F<t} estimated by empirical fraction; slope of log(frac) vs log(t)
    V = np.array([(F<t).mean() for t in ts])
    lt, lV = np.log(ts), np.log(np.clip(V,1e-12,None))
    # local slopes between consecutive points (small-t end is most reliable)
    sl = np.diff(lV)/np.diff(lt)
    return V, sl

cases = [
    ("TALL u=2>M2=1 (2,3,1,1)", 2,1,1,1, 1),
    ("WIDE u=1<M2=2 (1,2,2,2)", 1,2,2,1, 2),
    ("SQ   u=M2=2   (2,3,2,2)", 2,2,2,1, 3),
    ("WIDE u=1<M2=3 (1,3,3,3)", 1,3,3,1, 3),   # deeper wide: minAdm(1,3,3)=3? check
]
N=6_000_000
ts = np.array([1e-1,3e-2,1e-2,3e-3,1e-3,3e-4,1e-4])
for (label,u,M2,M3,b,minAdmRed) in cases:
    lamR_theory = minAdmRed/2.0
    Tstar=u+b
    FH = F_honest(u,M2,M3,b,N)
    FR = F_reduced(u,M2,M3,Tstar,N)
    VH,slH = slope_lambda(FH,ts)
    VR,slR = slope_lambda(FR,ts)
    print(f"\n=== {label} : theory lambda_R = minAdm/2 = {lamR_theory} ===")
    print("  t:        ", "  ".join(f"{t:.0e}" for t in ts))
    print("  Vol_H<t:  ", "  ".join(f"{v:.1e}" for v in VH))
    print("  Vol_R<t:  ", "  ".join(f"{v:.1e}" for v in VR))
    print("  slopeH(->0):", "  ".join(f"{s:.3f}" for s in slH))
    print("  slopeR(->0):", "  ".join(f"{s:.3f}" for s in slR))
    print(f"  [small-t slope] lambda_H ~ {slH[-1]:.3f}   lambda_R ~ {slR[-1]:.3f}   (theory {lamR_theory})")
