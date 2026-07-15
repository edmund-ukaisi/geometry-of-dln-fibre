"""
(A') Charge squeeze as EXACT algebra (PSD det-monotonicity), numeric spot-check skipping degenerate N.
(D') Genuine aligned-kernel seam:  P(2x3) head, last block a REAL matrix product F(3x2)E(2x2) so the seam
     is rank-constrained; H(3x2) free -> [H | FE] is 3x4. loss=||P[H|FE]||^2. Head P noninjective (2x3).
     Report rlct vs codim/2 of its zero set (computed by rank-path minimization).
"""
import numpy as np
from rlct_tools import CR
from rlct_is import is_rlct

print("(A') CHARGE SQUEEZE  det(N G N^T) in [lambda^b, Lambda^b]*det(NN^T),  G=DD^T >0")
rng=np.random.default_rng(1); nviol=0; ntest=0
for _ in range(300000):
    b=int(rng.integers(1,4)); rho=int(rng.integers(2,6)); d=rho+int(rng.integers(0,3))
    N=rng.normal(size=(b,rho)); Delta=rng.normal(size=(rho,rho)); U=rng.normal(size=(rho,d-rho))
    D=np.hstack([Delta,U]); G=D@D.T; ev=np.linalg.eigvalsh(G); lam,Lam=ev.min(),ev.max()
    dNN=np.linalg.det(N@N.T); dNGN=np.linalg.det(N@G@N.T)
    if dNN < 1e-6: continue          # skip near-singular N (float noise regime)
    ntest+=1
    if not (lam**b*dNN*(1-1e-8) <= dNGN <= Lam**b*dNN*(1+1e-8)): nviol+=1
print(f"   nondegenerate trials={ntest}, violations={nviol}  "
      f"(theorem: G>=lam I => NGN^T>=lam NN^T => det>=lam^b det(NN^T), det monotone on PSD) [{'PASS' if nviol==0 else 'FAIL'}]")

print()
print("(D') GENUINE aligned-kernel seam: loss=||P[H|FE]||^2, P:2x3, H:3x2, F:3x2, E:2x2")
def killmodel(a):
    P,H,F,E = a                       # P:2x3, H:3x2, F:3x2, E:2x2
    FE = np.einsum('nij,njk->nik', F, E)     # 3x2
    X = np.concatenate([H, FE], axis=2)      # 3x4
    Z = np.einsum('nij,njk->nik', P, X)      # 2x4
    return (Z**2).sum(axis=(1,2))
ts=[1e-3,1e-4,1e-5,1e-6,1e-7]
lf,lt,_=is_rlct([(2,3),(3,2),(3,2),(2,2)], killmodel, ts, N=500_000, reps=6, B=7, seed=41)
# codim of {P[H|FE]=0}: [H|FE] ranges over 3x4 matrices whose first 2 cols free, last 2 cols = rank<=2 (F E,
# inner dim 2 -> unconstrained since 2=min) -> [H|FE] is a FREE 3x4 matrix. So loss=||P*(3x4 free)||^2
# = 2-layer product (2,3,4). codim = CR((2,3,4),0).
cod = CR((2,3,4),0)
print(f"   rlct: fit={lf:.3f} tail={lt:.3f}   reduces to (2,3,4)-product, codim={cod}, codim/2={cod/2}")
print("   (E is 2x2 so FE=F*E spans all 3x2 -> [H|FE] free 3x4 -> not a genuine rank-constrained seam either)")

print()
print("(D'') TRUE rank-constrained seam: F:3x1, E:1x2 -> FE is 3x2 of RANK<=1 (genuine constraint).")
def seam_rank1(a):
    P,H,F,E = a                       # P:2x3, H:3x2, F:3x1, E:1x2
    FE = np.einsum('nij,njk->nik', F, E)     # 3x2 rank<=1
    X = np.concatenate([H, FE], axis=2)      # 3x4
    Z = np.einsum('nij,njk->nik', P, X)      # 2x4
    return (Z**2).sum(axis=(1,2))
lf,lt,_=is_rlct([(2,3),(3,2),(3,1),(1,2)], seam_rank1, ts, N=500_000, reps=6, B=7, seed=42)
print(f"   rlct: fit={lf:.3f} tail={lt:.3f}")
print("   zero set {P[H|FE]=0}, FE rank<=1: components via rank paths; compare to min-path codim/2.")
