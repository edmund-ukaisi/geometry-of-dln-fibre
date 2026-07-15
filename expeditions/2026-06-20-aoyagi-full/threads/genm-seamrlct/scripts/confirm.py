"""
Confirmations for the seam-rlct verdict.
 (A) Charge squeeze (Q4): exact linear algebra  lambda^b det(NN^T) <= det(N D D^T N^T) <= Lambda^b det(NN^T).
 (B) Scalar cross-peel counterexample (Q2): rlct(p^2 (h^2 + f^2 e^2)) = 1/2 (component {p=0}), via IS.
 (C) Full-loss IS rlct for the target probes (2,2,2,2),(2,3,3,3): expect codim/2 (homogeneous -> rlct_0=global).
 (D) KILL attempt: aligned-kernel deep intersection (Codex Q5 "most likely deficit"): 2-peel with a head
     whose kernel is aligned with both H and FE, spectator F rank-loss. Check rlct >= codim/2.
"""
import numpy as np
from rlct_tools import CR, minAdm
from rlct_is import is_rlct

print("="*78); print("(A) CHARGE SQUEEZE  lambda^b det(NN^T) <= det(N DD^T N^T) <= Lambda^b det(NN^T)")
print("="*78)
rng = np.random.default_rng(0)
worst = 1.0
for trial in range(200000):
    b, rho = rng.integers(1,4), rng.integers(2,6)   # N: b x rho, D: rho x d
    d = rho + int(rng.integers(0,3))
    N = rng.normal(size=(b, rho))
    # D = [Delta | U] full row rank rho (big cell): Delta invertible rho x rho, U rho x (d-rho)
    Delta = rng.normal(size=(rho,rho)); U = rng.normal(size=(rho, d-rho))
    D = np.hstack([Delta, U])
    G = D @ D.T
    ev = np.linalg.eigvalsh(G); lam, Lam = ev.min(), ev.max()
    detNN = np.linalg.det(N @ N.T)
    detNGN = np.linalg.det(N @ G @ N.T)
    if detNN <= 0: continue
    lo = lam**b * detNN; hi = Lam**b * detNN
    # check squeeze
    if not (lo - 1e-9*abs(lo) <= detNGN <= hi + 1e-9*abs(hi)):
        worst = min(worst, 0); print("  VIOLATION", b,rho,d, lo, detNGN, hi); break
else:
    print("  200000 random big-cell trials: squeeze holds EVERY time (bounded factor -> exponent unchanged). [PASS]")

print()
print("="*78); print("(B) SCALAR CROSS-PEEL  rlct(p^2 (h^2 + f^2 e^2))  expect 1/2 (min over components)")
print("="*78)
ts=[1e-3,1e-4,1e-5,1e-6,1e-7,1e-8]
def scal_crosspeel(a):
    p,h,f,e = a
    return (p[:,0]**2)*(h[:,0]**2 + (f[:,0]**2)*(e[:,0]**2))
lf,lt,_ = is_rlct([(1,),(1,),(1,),(1,)], scal_crosspeel, ts, N=700_000, reps=4, B=8, seed=11)
print(f"  rlct(p^2(h^2+f^2 e^2)): fit={lf:.3f} tail={lt:.3f}  expect 0.5")
# and rlct(h^2 + f^2 e^2) alone expect 1.0
def seam_scal(a):
    h,f,e = a
    return h[:,0]**2 + (f[:,0]**2)*(e[:,0]**2)
lf,lt,_ = is_rlct([(1,),(1,),(1,)], seam_scal, ts, N=700_000, reps=4, B=8, seed=12)
print(f"  rlct(h^2+f^2 e^2)     : fit={lf:.3f} tail={lt:.3f}  expect 1.0 (=codim/2, codim{{=0}}=2? no: comp {{h=0,e=0}} cod2, {{h=0,f=0}} cod2 -> 1.0)")

print()
print("="*78); print("(C) FULL DLN LOSS  rlct_0 (homogeneous => global) for target probes, via IS")
print("="*78)
def dln(a):
    Z=a[0]
    for L in a[1:]: Z=np.einsum('nij,njk->nik',Z,L)
    return (Z**2).sum(axis=(1,2))
print(f"  {'widths':>14} {'minAdm':>7} {'/2':>6} {'fit':>7} {'tail':>7}")
for widths in [(2,2,2),(2,2,2,2),(2,3,3,3),(3,3,3),(2,3,2),(3,2,3)]:
    shapes=[(widths[i],widths[i+1]) for i in range(len(widths)-1)]
    ma=minAdm(widths)
    lf,lt,_=is_rlct(shapes, dln, ts, N=700_000, reps=6, B=8, seed=20)
    flag="" if abs(lt-ma/2)<0.3 else "  <-- CHECK"
    print(f"  {str(widths):>14} {ma:>7} {ma/2:>6.2f} {lf:>7.3f} {lt:>7.3f}{flag}")

print()
print("="*78); print("(D) KILL ATTEMPT: aligned-kernel deep intersection (Codex Q5 'most likely deficit')")
print("  Model: head P (2x3) with a designed kernel; last-layer seam with spectator rank loss.")
print("  loss = || P * [H | F E] ||^2, P rank-deficient direction aligned with FE column-space.")
print("="*78)
# Construct: P in R^{2x3} but we FREELY vary P (its own layer). H:3x1 free, F:3x1 free, E:1x1 free.
# [H|FE] is 3x2. loss = ||P [H|FE]||^2 (2x2). Fully free P,H,F,E -> this is the (2,3,3,3)-flavoured 2-peel
# at a specific rank path. Compare rlct to the local codim of {P[H|FE]=0}.
def killmodel(a):
    P,H,F,E = a   # P:2x3, H:3x1, F:3x1, E:1x1
    FE = F * E[:,0][:,None,None]           # 3x1
    X = np.concatenate([H, FE], axis=2)    # 3x2
    Z = np.einsum('nij,njk->nik', P, X)    # 2x2
    return (Z**2).sum(axis=(1,2))
# what's codim{P[H|FE]=0}? this is a 2-peel DLN-like; compute by MC-free reasoning later; for now report rlct.
lf,lt,_ = is_rlct([(2,3),(3,1),(3,1),(1,1)], killmodel, ts, N=700_000, reps=6, B=8, seed=31)
print(f"  aligned-kernel model rlct: fit={lf:.3f} tail={lt:.3f}")
print("  (compare to codim/2 of its zero set -- computed separately)")
