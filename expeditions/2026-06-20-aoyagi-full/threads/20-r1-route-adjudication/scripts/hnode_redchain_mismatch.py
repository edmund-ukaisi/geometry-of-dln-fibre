"""
Q1 (THE crux) — does the geometric reduced core match the recursion's redChain?

The LayerSplit recursion (RouteMLayerSplit.lean) peels LAYER 1:
   minAdm(M₀,M₁,M₂,…) = min_{t≤min(M₀,M₁)} [ (M₀−t)(M₁−t) + minAdm(t,M₂,…) ]
i.e. the reduced chain is  redChain t M = (t, M₂, M₃, …)  — ONE FEWER LAYER.

For (3,3,4) [an L=2 chain, Fin 3]:  redChain t (3,3,4) = (t, 4)  [an L=1 leaf, Fin 2].
At the minimiser t=1:  redChain = (1,4),  minAdm(1,4) = 1·4 = 4.  block = (3-1)(3-1)=4.
So minAdm(3,3,4) = 4 + 4 = 8, value ½·8 = 4. (arithmetic checks)

But GEOMETRICALLY (hnode_recursion_shape.py), the clean rank-1 peel of (3,3,4) gives:
   nReg = 4 (the cleared pivot row, = M^(2) = 4 regular coords),  nReg/2 = 2,
   reduced core = ‖Δ·SC‖²  =  a (2,2,4) PRODUCT core, rlct = 2.
   total = 2 + 2 = 4.  ✓ value matches.

THE MISMATCH:
  - Recursion's reduced chain at t=1:  (1,4)  — a TWO-WIDTH LEAF, minAdm = 4, "rlct" 2.
  - Geometry's reduced core:           ‖Δ·SC‖² — a (2,2,4) product core, rlct 2.
These give the SAME VALUE (2) but are DIFFERENT OBJECTS:
  dlnLoss(1,4) 0 = ‖a (1×4) matrix‖² = ∑ of 4 squares  → smooth, rlct 2 trivially (Morse, dim 4).
  ‖Δ·SC‖²        = (2,2,4) product singularity         → rlct 2 by NON-TRIVIAL radial resolution.

So redEmbed : Y ≃ₜ Params (redChain 1 (3,3,4)) = Params(1,4) demands a MEASURE-PRESERVING
HOMEOMORPHISM from the (2,2,4)-core coordinates onto the (1,4) leaf coordinates such that
   G(y)² = ‖Δ·SC‖²(y)  =  dlnLoss(1,4) 0 (redEmbed y)  =  ‖(1×4 matrix)‖²(redEmbed y).
This is FALSE: a (2,2,4) product singularity (rlct 2, but with θ multiplicity / non-Morse
structure) is NOT measure-preservingly homeomorphic to a smooth (1,4) sum-of-squares.
The VALUES of rlct agree (2=2) but the GERMS are not isomorphic.
"""
import sympy as sp
from itertools import product as iproduct

def minAdm_bruteforce(M):
    """minAdm via Aoyagi: min over weakly-decreasing rank profiles t (t_L=0) of Mval(t)."""
    L = len(M)-1
    # t : (t_1,...,t_L), t_L=0, weakly decreasing, t_j ≤ min over admBound
    # admBound: t_1 ≤ min(M_0,M_1); t_j ≤ min(t_{j-1}, M_{j+1})? Use the recursion directly.
    return minAdmRec(M)

def minAdmRec(M):
    L = len(M)-1
    if L == 0: return 0
    if L == 1: return M[0]*M[1]
    best = None
    for t in range(min(M[0],M[1])+1):
        red = [t] + list(M[2:])
        v = (M[0]-t)*(M[1]-t) + minAdmRec(red)
        best = v if best is None else min(best,v)
    return best

print("minAdm(3,3,4) =", minAdmRec([3,3,4]), " (½ =", sp.Rational(minAdmRec([3,3,4]),2), ")")
print("redChain at t=1: (1,4), minAdm(1,4) =", minAdmRec([1,4]), " block=(3-1)(3-1)=4, total=", 4+minAdmRec([1,4]))
print()

# Newton-LP rlct of the (2,2,4) product core ‖Δ·SC‖² resolved (radial {SC=0} blow-up).
# vs the smooth (1,4) leaf ‖(1×4)‖² (Morse, rlct = 4/2 = 2).
print("=== rlct VALUES agree (both 2) but GERMS differ ===")
print("dlnLoss(1,4) at 0 = ∑_{j} a_j²  (4 squares, a smooth Morse quadratic of dim 4): rlct = 4/2 = 2.")
print("‖Δ·SC‖² = (2,2,4) product core: rlct = 2 by RADIAL resolution (a genuine singularity,")
print("  Δ free 2×2, SC free 2×4 — NOT a smooth quadratic; its zero set {Δ·SC=0} is a")
print("  determinantal-type variety, not a linear subspace).")
print()
print("redEmbed must be a MEASURE-PRESERVING HOMEOMORPHISM Params(2,2,4-core) ≃ Params(1,4)")
print("with G²=dlnLoss(1,4)∘redEmbed.  But the (2,2,4)-core germ is NOT homeomorphic to the")
print("smooth (1,4) germ (different singularity types, even though same rlct value). So the")
print("hnode datum's redCore_eq + redEmbed CANNOT be honestly discharged at this node.")
print()
print("CONCLUSION FOR Q1:")
print("  hnode as a per-node Schur form with G² = dlnLoss(redChain) is provable ONLY when")
print("  the geometric reduced core IS (measure-pres. homeomorphic to) the width-chain")
print("  reduced loss. That holds for the RANK-1 chain (2,2,...,2) where redChain (2,2,..)")
print("  -> the fresh core IS a (2,2,...) chain loss. It FAILS at (3,3,4) where the geometric")
print("  reduced core is a (2,2,4) PRODUCT singularity but redChain says (1,4) LEAF.")
