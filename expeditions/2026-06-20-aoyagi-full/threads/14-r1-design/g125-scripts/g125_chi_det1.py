import sympy as sp
# The naive generator-replacement χ has det=(w0+1)²(w4+1) — a UNIT, not ±1. For a114e07e's
# MeasurePreserving interface, do we need det=±1, or is unit-Jacobian enough?
#
# TWO honest options, both sound for RLCT:
# (A) det=±1 MEASURE-PRESERVING χ via SHEARS (like lemma2Fwd): solve the regular gens by ELEMENTARY
#     transvections (each xi -> xi + poly(others), det=1). This gives literal MeasurePreserving.
# (B) unit-Jacobian (det=unit) χ via generator-replacement: transports rlctAtOn via rlct_unit_invariant
#     (the |Jac| unit factor is absorbed). Lighter but NOT MeasurePreserving.
#
# Which does the deepest-point split admit? The regular generators gi = wi_pivot + (higher order).
# A SHEAR solving gi=0 sets wi_pivot -> wi_pivot - (higher order)/... but the "higher order" CONTAINS
# wi_pivot (e.g. g00 = w4(1+w0) + (w0+w1 w6), so solving for w4 gives w4 = (E1 - w0 - w1 w6)/(1+w0) --
# a DIVISION by the unit (1+w0), NOT a pure shear). So the clean det=1 shear is NOT directly available;
# the unit pivot (1+w0) is a UNIT but not 1, so the inverse is division-by-unit => det = unit, not ±1.
#
# Let me check: CAN we rescale to get det=±1? The issue is the cross-term w0*w4 (the (0,0) entry's
# bilinearity). At the deepest point, P_11 = (I+X1)S_11 + ... and S_11 = I + (higher) is a unit MATRIX,
# not the identity. So the regular block's change involves MULTIPLYING by the unit matrix S_11 --
# det = det(S_11)^(something), a UNIT, not 1.
print("=== Does the deepest split admit a det=±1 (MeasurePreserving) χ, or only unit-Jacobian? ===")
print("The regular generators involve the UNIT MATRIX S_11 = I + higher (not identity): e.g.")
print("g00 = w4(1+w0) + ... => solving w4 = (E1-...)/(1+w0), division by the unit (1+w0).")
print("=> the natural χ has det = a UNIT (e.g. (w0+1)²(w4+1)), NOT ±1. It is unit-Jacobian, NOT")
print("literally measure-preserving.")
print()
print("HONEST CONSEQUENCE for the consumers:")
print(" - a114e07e's schur_recursion_step_sound: if it REQUIRES MeasurePreserving (det=±1), the natural")
print("   χ does NOT satisfy it. It should instead use the UNIT-JACOBIAN transport (rlct_unit_invariant_aux)")
print("   — rlctAtOn is invariant under a unit-Jacobian analytic diffeo (the |Jac| unit factor absorbed).")
print("   OR: factor χ = (det=±1 shear part) ∘ (diagonal unit rescale), and absorb the rescale as a unit.")
print(" - fm-2's schur_chart_exists: the (uᵢ,ψᵢ) adapted basis IS unit-Jacobian (the unit pivots), not")
print("   det=±1. Same resolution: unit-Jacobian transport, not MeasurePreserving.")
print()
# VERIFY: is rlctAtOn transport under unit-Jacobian available green? (rlct_unit_invariant_aux: rlctAt(u·F)
# = rlctAt(F) for u a unit -- that's the INTEGRAND unit, slightly different from a unit JACOBIAN c-o-v.)
# The c-o-v with unit Jacobian: ∫|F|^{-c} = ∫|F∘χ⁻¹|^{-c}|Jac χ⁻¹|, and |Jac| a unit (bdd above/below)
# => same rlct (the unit weight is bounded, doesn't shift the threshold). This is the weightedThreshold
# with a unit weight — S1's rlctAtOn_comp + unit-weight invariance.
print("The right Lean tool: rlctAtOn transport under a unit-Jacobian analytic diffeo (the |Jac χ| unit")
print("weight, bounded above+below, doesn't shift the threshold) — NOT MeasurePreserving (det=±1).")
print("So flag to a114e07e: the χ is unit-Jacobian, the interface should be unit-Jacobian transport,")
print("not strict MeasurePreserving — unless they want the (det=±1 shear)∘(unit rescale) factorization.")
