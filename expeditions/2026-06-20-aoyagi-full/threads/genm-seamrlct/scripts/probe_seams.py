"""
PROBE 1: exact rlct of seam models via the paper's theorems, cross-checked numerically.
PROBE 2: matrix-product base rlct(||FE||^2) vs codim/2 for a table of dims -- can it drop below?
PROBE 3: numeric global rlct of the full DLN loss ||Z||^2 for the target chains vs minAdm/2.
"""
import numpy as np
from rlct_tools import CR, minAdm, rlct_matprod, tube_rlct, box_sampler, dln_loss, product_of_layers

print("="*78)
print("PROBE 0: sanity -- numeric estimator on KNOWN cases (sum of e squares -> e/2)")
print("="*78)
for e in [1,2,3,4]:
    smp = box_sampler([(e,)], box=1.0)
    loss = lambda Ls: (Ls[0]**2).sum(axis=1)
    lam, fine, tab = tube_rlct(smp, loss, ts=[1e-2,4e-3,1.6e-3,6.4e-4,2.56e-4], N=3_000_000, seed=1)
    print(f"  x1^2+..+x{e}^2 : rlct_fit={lam:.3f} fine={fine:.3f}  expect {e/2}")

print()
print("="*78)
print("PROBE 1: (2,2,2) seam model  loss ~ ||H||^2 + ||FE||^2  (design's benign example)")
print("="*78)
# EXACT via theorems: H in R^2 (rlct 1), ||FE||^2 with F in R^{2x1}, E in R^{1x1}:
#   ||FE||^2 = ||F||^2 * E^2 ; rlct = min(rlct(||F||^2)=1, rlct(E^2)=1/2) = 1/2  [S2]
# total = 1 + 1/2 = 3/2 = CR((2,2,2),0)/2
print(f"  EXACT: rlct(||H||^2)=1, rlct(||F||^2 E^2)=min(1,1/2)=1/2 -> total 3/2")
print(f"  CR((2,2,2),0)/2 = {minAdm((2,2,2))/2}")
# numeric on the model loss ||H||^2 + ||FE||^2  (H:2, F:2, E:1)
def seam222(Ls):
    H,F,E = Ls
    return (H**2).sum(1) + (F**2).sum(1)*(E[:,0]**2)
smp = box_sampler([(2,),(2,),(1,)], box=1.0)
lam,fine,tab = tube_rlct(smp, seam222, ts=[1e-2,4e-3,1.6e-3,6.4e-4,2.56e-4,1e-4], N=6_000_000, seed=2)
print(f"  NUMERIC seam model: rlct_fit={lam:.3f} fine={fine:.3f}  (expect 1.5)")

print()
print("="*78)
print("PROBE 2: matrix-product base rlct(||FE||^2) vs codim/2  (F:m x q, E:q x n)")
print("  KILL TEST: does rlct(||FE||^2) EVER fall below codim/2? (would be a wall base case)")
print("="*78)
def matprod_loss(m,q,n):
    smp = box_sampler([(m,q),(q,n)], box=1.0)
    def loss(Ls):
        F,E = Ls
        Z = np.einsum('nij,njk->nik', F, E)
        return (Z**2).sum(axis=(1,2))
    return smp, loss
print(f"  {'(m,q,n)':>12} {'codim':>6} {'codim/2':>8} {'rlct_fit':>9} {'fine':>7}")
for (m,q,n) in [(2,1,1),(2,2,2),(3,2,3),(2,3,2),(3,3,3),(2,2,3),(4,2,4),(3,1,3),(4,2,2),(2,4,2),(3,2,4)]:
    cod = CR((m,q,n),0)
    smp,loss = matprod_loss(m,q,n)
    # small box so degeneracies are common; importance-ish by shrinking box
    lam,fine,tab = tube_rlct(smp, loss, ts=[4e-3,1.6e-3,6.4e-4,2.56e-4,1e-4], N=6_000_000, seed=3, )
    flag = "" if abs(fine-cod/2)<0.15 or abs(lam-cod/2)<0.15 else "  <-- CHECK"
    print(f"  {str((m,q,n)):>12} {cod:>6} {cod/2:>8.2f} {lam:>9.3f} {fine:>7.3f}{flag}")

print()
print("="*78)
print("PROBE 3: full DLN loss ||Z||^2, GLOBAL rlct (deep origin) vs minAdm/2")
print("  target chains + neighbours")
print("="*78)
print(f"  {'widths':>14} {'minAdm':>7} {'minAdm/2':>9} {'rlct_fit':>9} {'fine':>7}")
for widths in [(2,2,2),(2,2,2,2),(2,3,3,3),(3,3,3),(2,2,3),(2,3,2),(3,2,3),(2,2,2,2,2),(2,3,4,3,2)]:
    ma = minAdm(widths)
    smp,loss = dln_loss(widths, box=1.0)
    # deeper degeneration is rare -> use smaller box to raise event rate for longer chains
    box = 0.7 if len(widths)>=4 else 1.0
    smp,loss = dln_loss(widths, box=box)
    lam,fine,tab = tube_rlct(smp, loss, ts=[4e-3,1.6e-3,6.4e-4,2.56e-4,1e-4], N=8_000_000, seed=4)
    flag = "" if abs(fine-ma/2)<0.2 or abs(lam-ma/2)<0.2 else "  <-- CHECK"
    print(f"  {str(widths):>14} {ma:>7} {ma/2:>9.2f} {lam:>9.3f} {fine:>7.3f}{flag}")
