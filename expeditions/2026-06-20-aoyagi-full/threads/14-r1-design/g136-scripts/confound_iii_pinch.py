# The PINCH case (5,1,5): C1 (5x1), C2 (1x5). product = C1 C2 = rank-1 5x5 outer product, =0 iff C1=0
# or C2=0. {prod=0} = {C1=0} ∪ {C2=0}, two components each codim 5. minAdm=5, claimed rlct=5/2.
# This is the genuine STUCK-DESCENT candidate: the first factor C1 is 5x1 (a column). Blow up {C1=0}
# (codim 5). Hard pivot c0=1. Schur straighten: C1=(1,a,b,c,d)^T, clear "col 0" -> but C1 is a COLUMN,
# the Schur complement of a 5x1 with pivot is EMPTY (0x0)? The reduced first factor is 4x0 = empty.
# Does the recursion close? f = ‖C1 C2‖^2 = ‖C1‖^2 ‖C2‖^2 (outer product norm). = (Σc_i^2)(Σd_j^2).
# This is a PRODUCT of two smooth blocks (Fubini!), NOT a blow-up case. The recursion should detect
# this. Verify the rlct via the product-min rule:
import sympy as sp
# rlct of (Σ_{i=0}^{4} c_i^2)(Σ_{j=0}^{4} d_j^2) at origin. Disjoint vars => Fubini product.
# Each factor: smooth block of 5 squares, rlct = 5/2. Product of two on disjoint vars:
# rlct(G·H) where G,H smooth blocks on disjoint vars = ? NOT min, NOT sum in general for the SAME point.
# ∫(GH)^{-c} = ∫G^{-c} ∫H^{-c}; G^{-c} integrable iff c<5/2, same H => product finite iff c<5/2 => rlct=5/2.
# = min(5/2,5/2)=5/2. MATCHES minAdm/2=5/2. GOOD -- but via PRODUCT-MIN (Fubini), not blow-up recursion!
print("(5,1,5): f = ‖C1‖²·‖C2‖² (rank-1 outer product norm = product of two 5-square blocks).")
print("  rlct = 5/2 via Fubini product-min (disjoint vars), matches minAdm/2 = 5/2.")
print("  *** This is NOT resolved by first-factor blow-up -- it's a PRODUCT SEPARATION. ***")
print()
# THE OBSTRUCTION CANDIDATE: width-1 middle layers make the chain SEPARATE (product structure), which
# the first-factor blow-up recursion does NOT handle (it assumes coupled variables). Is this a WALL?
# Check: (2,1,2): f = ‖C1 C2‖^2, C1 2x1, C2 1x2. product rank<=1, = C1 C2 (2x2 outer). 
# ‖C1 C2‖^2 = ‖C1‖^2 ‖C2‖^2 = (a0^2+a1^2)(b0^2+b1^2). DISJOINT => Fubini, rlct=min(1,1)=1=minAdm/2=2/2 ✓.
# This is the KNOWN (2,1,2) Fubini-product case (r1-general-atlas flagged it). So width-1 layers
# trigger PRODUCT SEPARATION, a DIFFERENT mechanism than the blow-up cover. The recursion must branch:
# if a layer width is 1 (or the factor separates), use Fubini, NOT blow-up.
import numpy as np
rng=np.random.default_rng(3)
# verify ‖C1 C2‖^2 = ‖C1‖^2‖C2‖^2 for rank-1 (width-1 middle):
for (m1,m3) in [(5,5),(2,2),(3,4)]:
    C1=rng.standard_normal((m1,1)); C2=rng.standard_normal((1,m3))
    lhs=np.linalg.norm(C1@C2)**2; rhs=(np.linalg.norm(C1)**2)*(np.linalg.norm(C2)**2)
    print(f"({m1},1,{m3}): ‖C1C2‖²={lhs:.4f} = ‖C1‖²‖C2‖²={rhs:.4f}? {abs(lhs-rhs)<1e-9}  => SEPARATES (Fubini, not blow-up)")
