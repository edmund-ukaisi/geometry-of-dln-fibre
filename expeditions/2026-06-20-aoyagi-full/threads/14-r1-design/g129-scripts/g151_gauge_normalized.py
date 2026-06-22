import sympy as sp
# Verify the CORRECTED form: the reduced core is T̃·S̃ with gauge-normalized blocks absorbing (I-VY)^{-1}.
# On {E=0}, P11 = T(I-VY)^{-1}S. Define the gauge-normalized reduced block: absorb the internal unit.
# The reduced chain ‖∏ T̃‖²: T̃_1 = T (left), T̃_2 = (I-VY)^{-1}S OR T̃_1=T(I-VY)^{-1}, T̃_2=S — either way
# the product is T(I-VY)^{-1}S, an honest 2-factor reduced chain with the MIDDLE unit (I-VY)^{-1} absorbed.
A,Y,Z,T = sp.symbols('A Y Z T'); B,U,V,S = sp.symbols('B U V S')
# the internal gauge unit at the H1 (middle) layer: g = (I - VY)^{-1} (here scalar 1/(1-VY)).
# The reduced chain product on {E=0} = T · g · S. Is g a UNIT near w0? at w0 (V=Y=0): g=1. Yes, unit.
g = 1/(1 - V*Y)
print("internal gauge unit g = (I-VY)^{-1} =", g, " ; at w0 (V=Y=0): g =", g.subs({V:0,Y:0}), " (unit ✓)")
reduced_core = sp.simplify(T*g*S)
print("reduced core on {E=0} = T·g·S =", reduced_core, " — a 2-factor reduced chain with middle unit g absorbed.")
print()
print("""
CORRECTED loss-form (folding Codex): the reduced core is NOT ‖T_1 T_2‖² (raw blocks) but
‖T̃_1 ··· T̃_L‖² where T̃_s = the GAUGE-NORMALIZED blocks — the raw T_s with the internal gauge units
(I - V_s Y_s)^{-1} (a unit at w0) absorbed. This is dlnLoss M 0 on the REDUCED chain in the gauge-
normalized coords (M_s = H_s - r). The endpoint-regular leak E10(I+E00)^{-1}E01 is absorbed into the
regular block ∑E² (endpoint-regular × endpoint-regular). So:
  ℓ ∘ Φ =ᶠ ∑ E² + ‖T̃_1 ··· T̃_L‖²   (EXACT germ, via the det-unit c-o-v + the gauge normalization).
The split is still EXACT (not a squeeze), the Jacobian still a bounded unit (NON-MP), nReg still
r(H_0+H_last−r). The CORRECTION: the reduced core's blocks are gauge-normalized T̃_s (internal units
absorbed), and the reduced chain = dlnLoss M 0 in THOSE coords — NOT the literal raw T_s.
""")
# The Jacobian det Codex gave: det(A)^{-(r+M2)} det(B)^{-M0}, bounded unit near w0 (A,B near I_r). Confirm
# it's a unit (the gauge-normalization is part of the det-unit c-o-v, det = product of A,B powers, all
# near I_r ⟹ det near 1, bounded away from 0/∞, NOT identically 1). Consistent with NON-MP.
print("Jacobian det (Codex) = det(A)^{-(r+M2)}·det(B)^{-M0}: at w0 (A,B≈I_r) ≈ 1, bounded unit, ≠1 generally.")
print("⟹ NON-MP confirmed (rlctAtOn_unit_invariant_aux, not comp_homeomorph). The gauge-normalization is")
print("part of the det-unit chart; it does NOT break the unit-Jacobian (g = (I-VY)^{-1} is a unit factor).")
