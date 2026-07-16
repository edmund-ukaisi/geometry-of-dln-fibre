"""
satred FINAL accounting confirmation (correct b = M1 - u, u = M0 at saturation a=0).

Claims to confirm:
  (1) The honest saturated integral I equals RMBTF(M) restricted to the {P invertible} chart, so
      lambda_H = 1/2 minAdm(M) EXACTLY (no drop below the needed threshold). Because
      z_tilde0 = [P|B12][z0;A_cor] = X*Y with X = full M0xM1 first layer, Y = full M1xM2 second
      layer, so frobSq(z_tilde0 * Zdeep) = frobSq(prod(M)) on the {P invertible} chart.
  (2) The det-P->0 region contributes FINITELY (compensated by B12 keeping X=[P|B12] full row
      rank M0): measure of {|det P|<delta} contribution to I stays bounded as delta->0.
  (3) The density rho(z_tilde0) of X*Y has RLCT cost Delta = 1/2(minAdm(redChain u M) - minAdm(M)):
      compare lambda_H (honest) to lambda_R (reduced RMBTF(redChain)) = 1/2 minAdm(redChain).
"""
import numpy as np
rng = np.random.default_rng(5)

def minAdmRec(M):
    M=list(M); L1=len(M)
    if L1==1: return 0
    if L1==2: return M[0]*M[1]
    best=None
    for t in range(min(M[0],M[1])+1):
        red=[t]+M[2:]
        v=(M[0]-t)*(M[1]-t)+minAdmRec(red)
        best=v if best is None else min(best,v)
    return best

def lam_slope(F, ts):
    V=np.array([(F<t).mean() for t in ts])
    return np.diff(np.log(np.clip(V,1e-12,None)))/np.diff(np.log(ts))

def honest_F(M, N):
    # M = (M0,M1,M2,M3) arity-4; u=M0 (a=0 saturation, assume M0<=M1), b=M1-M0
    M0,M1,M2,M3=M
    b=M1-M0
    P=rng.uniform(-1,1,(N,M0,M0)); B12=rng.uniform(-1,1,(N,M0,b)) if b>0 else np.zeros((N,M0,0))
    X=np.concatenate([P,B12],axis=2)          # M0 x M1
    Y=rng.uniform(-1,1,(N,M1,M2))
    z1=rng.uniform(-1,1,(N,M2,M3))
    Z=np.einsum('nij,njk->nik',X,Y)
    Pr=np.einsum('nij,njk->nik',Z,z1)
    return (Pr**2).sum((-1,-2)), np.abs(np.linalg.det(P))

def reduced_F(M, Tstar, N):
    M0,M1,M2,M3=M
    W=rng.uniform(-Tstar,Tstar,(N,M0,M2)); z1=rng.uniform(-1,1,(N,M2,M3))
    Pr=np.einsum('nij,njk->nik',W,z1)
    return (Pr**2).sum((-1,-2))

ts=np.array([1e-2,3e-3,1e-3,3e-4,1e-4])
cases=[(1,2,3,3),(1,3,3,3),(2,3,2,2),(1,4,4,4),(1,2,2,2),(2,4,3,3)]
print(f"{'M':>14} {'minAdm(M)':>9} {'minAdmRed':>9} {'need=mM/2':>9} {'lamR/2':>7} {'Delta':>6} "
      f"{'lam_H(meas)':>11}")
for M in cases:
    M0,M1,M2,M3=M
    mM=minAdmRec(list(M)); mR=minAdmRec([M0,M2,M3])
    Delta=(mR-mM)/2.0
    FH,_=honest_F(M,6_000_000)
    slH=lam_slope(FH,ts)
    print(f"{str(M):>14} {mM:>9} {mR:>9} {mM/2:>9.2f} {mR/2:>7.2f} {Delta:>6.2f} "
          f"{slH[-1]:>8.3f}    (trend {np.array2string(slH,precision=2)})")

print("\n=== (2) det-P->0 contribution to I stays finite (M=(1,3,3,3), c'=1.3<1.5) ===")
M=(1,3,3,3); cp=1.3
FH,detP=honest_F(M,6_000_000)
g=FH**(-cp)
for delta in [0.3,0.1,0.03,0.01]:
    mask=detP<delta
    contrib=g[mask].mean()*mask.mean() if mask.sum()>0 else 0.0  # ~ mean over ALL * P(small)
    print(f"  |detP|<{delta}: frac={mask.mean():.3f}  E[g*1(small)]={ (g*mask).mean():.4f} "
          f"(total E[g]={g.mean():.4f})")
