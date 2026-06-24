"""
Q1 — CAREFUL re-derivation of the geometric reduced core at (3,3,4), t=1.

Aoyagi Lemma 2 / Theorem 3 product reduction: near a rank-r product, block-elim
gives diag(C1_r, ∏C^(s)) where C^(s) are REDUCED-width matrices M^(s)×M^(s+1) with
the rank-r regular block split off. For the CORE at the deepest point (rank 0... but
Theorem 4 says resolve at origin where all intermediate ranks = r=0).

Wait — the core ‖∏C^(s)‖² is resolved at the ORIGIN (all C=0). The blow-up RECURSION
(Cases 1&2) is what introduces the rank profile t. Let me follow the LayerSplit
recursion's geometry: it peels LAYER 1 at leading-pivot rank t.

For (3,3,4) [C¹ 3×3, C² 3×4], peel layer 1 at rank t=1:
The blow-up exposes a t×t = 1×1 unit pivot in C¹; the layer-1 block codim is
(M₀-t)(M₁-t) = (3-1)(3-1) = 4 (the α/incidence divisor's exponent).
The reduced chain is redChain 1 (3,3,4) = (1, 4): a fresh core ‖X·C²'‖² where
X is 1×1 (=t×t survivor) ... NO. Let me get the arity right.

redChain t M = (t, M₂, M₃, ..., M_L), so (1,4): C̃¹ is 1×4 (t × M₂ = 1×4).
dlnLoss(1,4) 0 = ‖C̃¹‖² = ‖a 1×4 matrix‖² = 4 squares.  THIS is what the recursion claims.

BUT the verify-r1-light c334_peel.py result (cited in the design cert) says:
   F ∼ ‖T‖² + ‖Δ·S‖²,  T clean 1×4, Δ free 2×2, S free 2×4.
The ‖Δ·S‖² is the (2,2,4) part. Where does it go in the recursion?

RESOLUTION: the recursion's redChain (1,4) is the CLEAN T-part ONLY (the t=1 pivot row,
1×4 = 4 coords). The Δ·S coupled part is the LAYER-1 BLOCK being blown up — its codim
(3-1)(3-1)=4 is the α-divisor exponent. In the LayerSplit value-fold, the block codim
4 is ADDED as a leaf divisor, and minAdm(redChain)=minAdm(1,4)=4 is the recursive part.
Total 4+4 = 8. ✓

So the recursion SPLITS (3,3,4) as: block-divisor codim 4 (the Δ·S coupled (2,2,4) part,
counted as a SINGLE divisor of exponent 4) + reduced leaf (1,4) codim 4.

NOW the squeeze/hnode question: a single hnode step gives rlct = nReg/2 + rlct(G²).
For the value to be 4 = 2+2, we need nReg/2 = 2 and rlct(G²)=2, i.e. nReg=4, G²=reduced.
The nReg=4 regular coords = the cleared pivot ROW T (1×4) — fine, that's smooth.
The reduced G² must be the (1,4) leaf? No — (1,4) leaf is ITSELF smooth (4 squares),
rlct = 4/2 = 2, but that's ANOTHER nReg/2, not a recursive core.

The DANGER: the coupled Δ·S (2,2,4) part (codim 4, the part that needs RADIAL resolution
to get rlct 2, NOT additive 4/2=2 of smooth coords) — is it correctly handled?
The (2,2,4) core ‖Δ·S‖²: 4 free + 8 free = 12 coords, but rlct = 2 (not 12/2=6!).
So the Δ·S part is GENUINELY singular: its 12 coords resolve to rlct 2, far below 6.
A per-node SMOOTH split (nReg/2) would count it as 12/2 = 6 — WRONG.
"""
import sympy as sp
import numpy as np
from scipy.optimize import linprog

def minAdmRec(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec([t]+list(M[2:])) for t in range(min(M[0],M[1])+1))

print("minAdm(2,2,4) =", minAdmRec([2,2,4]), "-> rlct(2,2,4 core) = ½·", minAdmRec([2,2,4]),
      "=", sp.Rational(minAdmRec([2,2,4]),2))
print("  (the (2,2,4) product core ‖Δ·S‖² has rlct = ½·minAdm(2,2,4) = 2, by the SAME headline)")
print()
print("So ‖Δ·S‖² (2,2,4 core) rlct = 2; the smooth count 12/2 = 6 is WRONG.")
print("A hnode SMOOTH (nReg/2) split that swallowed the Δ·S coords as 'regular' would give 6.")
print()
print("=== The decisive structural question for hnode ===")
print("hnode requires the cross term = bcol⊗Erow (RANK-1) and G² = reduced loss.")
print("At (3,3,4) t=1, the coupled part is ‖Δ·S‖², Δ free 2×2 — a rank-2 bilinear core,")
print("NOT a rank-1 outer product. So:")
print(" • If hnode treats Δ·S coords as part of the nReg SMOOTH block: counts 6, WRONG (overcounts).")
print(" • If hnode puts Δ·S into G² (the reduced core): then G² = ‖Δ·S‖² is a (2,2,4) PRODUCT")
print("   singularity, NOT dlnLoss(redChain=(1,4)) [a smooth 4-square leaf]. redCore_eq FAILS.")
print(" • The hard-1-pivot rank-1 cross term bcol⊗Erow cannot REPRESENT the rank-2 Δ coupling.")
print()
print("=> hnode (rank-1 Schur node form + G²=dlnLoss(redChain)) is UNPROVABLE at corank-≥2")
print("   nodes. It is faithful ONLY for corank-≤1 peels (rank-1 chains, c₁=0 full-rank).")
