import sympy as sp
from fractions import Fraction as Fr
# CONFOUND CHECK (controller's correction): is R1's per-cell datum the LIGHT monomial pullback
# (x_p²·reduced, MIN-folded) or the HEAVY additive IsSchurStraightenSqueeze (nReg/2 + reduced)?
#
# The (2,2,2) leaf evidence: rlctAtOn(myF222) 0 = 3/2 = min over monomial axes (Case222 rlctAtOn_myF222_le
# = the MIN form; the leaf integrand = monomialIntegrand · unit, threshold = ⨅ axisRatio).
#
# The C1 node mechanism (g183/G2 node_loss_pivot_factor): pivotBlowupOn active p gives
#   core ∘ φ = x_p² · (core ∘ hardPivotAt)   [the MONOMIAL PULLBACK, x_p the exceptional axis]
# with Jacobian (x_p)^(card−1). So the per-cell consequence on the chart is:
#   |core∘φ|^{-c} · |Jac| = |x_p|^{2·(-c)} · |x_p|^{card-1} · |reduced∘φ|^{-c}
#   = monomialIntegrand on the x_p axis (k=1, h=card-1, ratio card/2) × (reduced pullback).
# The rlct of THIS = MIN(axisRatio of x_p = card/2, rlct of reduced). Recurse → MIN-fold = foldDivisors.
print("R1 per-cell datum = the MONOMIAL PULLBACK (pivotBlowupOn):")
print("  core ∘ φ = x_p² · (core ∘ hardPivotAt)   [G2 node_loss_pivot_factor, x_p exceptional]")
print("  Jacobian (x_p)^(card-1)  ⟹  per-cell axis (k,h)=(1, card-1), ratio = card/2 = codim/2.")
print("  rlct(cell) = MIN(codim/2, rlct(reduced))  → recurse → foldDivisors MIN-fold. ✓ LIGHT.")
print()
print("This is LIGHTER than the heavy additive IsSchurStraightenSqueeze (nReg/2 + rlctAtOn(reduced)):")
print("  - LIGHT (R1 core): pivotBlowupOn monomial pullback x_p²·reduced; per-cell DATUM = node_loss_pivot_factor")
print("    (G2, fm3 banked) + node_jacobian_det. The value MIN-folds (foldDivisors). NO squeeze constants.")
print("  - HEAVY (off-path/L2): IsSchurStraightenSqueeze (c₁Φ≤flatCore≤c₂Φ, additive nReg/2 + reduced).")
print("    This is the DEEPEST-GAUGE / L2 regular-shift datum (the g150/g175 squeeze), NOT R1's blow-up node.")
print()
# So the controller is RIGHT: R1's per-cell datum is the light monomial pullback, the heavy squeeze is L2.
# CHECK against (2,2,2): the C1 nodes are pivotBlowupOn (step1A={0,1,2,3}p0, step2={1,2,3}p1). Their
# per-cell datum = myF222_step1A (x_p²·Q) + step1A_det (x_p³). LIGHT, monomial. NOT a squeeze.
print("(2,2,2) check: step1A = pivotBlowupOn{0,1,2,3}0, myF222_step1A: myF222(φ)=y0²·Q [monomial pullback],")
print("  step1A_det: |det|=y0³ [Jacobian]. The per-cell datum is THESE (G2-shape), light. The squeeze")
print("  (core_comparability_squeeze, #54) is the DEEPEST-GAUGE chart (L2/full-B), a DIFFERENT node.")
print()
print("VERDICT: controller + fm3 RIGHT. R1 per-cell datum = LIGHT monomial pullback (node_loss_pivot_factor")
print("+ node_jacobian_det, fm3's banked G2). The heavy IsSchurStraightenSqueeze is the off-path L2 datum.")
print("g183 §6 over-specified the datum as the heavy squeeze — correct to the light monomial pullback.")
print("The COMBINATORIAL recipe + codim-design (§1/§2/§4/§VALUE-TARGET) are datum-WEIGHT-INDEPENDENT — unchanged.")
