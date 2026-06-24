<task>
Lean/Mathlib RLCT proof, deep linear networks. A SIMPLIFICATION that CONTRADICTS the blessed cert — I
need it adjudicated before I build, because getting MP-vs-non-MP wrong wastes the construction.

SETUP. L layers gauge-sliced C_s = [[I_r+X_s, Y_s],[Z_s, T_s]]. The reduced "core" is the per-layer
SCHUR complement S_s = T_s − Z_s(I+X_s)⁻¹Y_s (this was just confirmed correct, #61, replacing a wrong
multiplicative-unit form T_s·(I−V_sY_s)⁻¹). The RLCT proof structure (design D):
 - `split`: MP reindex flat-coords ⟶ (reg residuals) × (raw core T_s) × (spectator gauge X_s,Y_s,Z_s).
 - `coreAbsorb`: a self-homeo of the split-space turning the raw core T_s into the Schur S_s, fixing
   the reg + spectator slots. The cert says coreAbsorb is NON-MP with unit Jacobian det(I−VY)⁻ᴹ⁰.
 - `coreAbsorb_rlct`: absorbed-core RLCT = raw-core RLCT (cert: via a |det| unit-weight peel).

MY CLAIM (contradicts cert's "non-MP"): the CORRECT (additive Schur) coreAbsorb is MEASURE-PRESERVING,
because S_s = T_s − Z_s(I+X_s)⁻¹Y_s is AFFINE in T_s — the subtracted term Z_s(I+X_s)⁻¹Y_s involves only
X_s,Y_s,Z_s (the gauge/spectator blocks), NOT T_s. So for fixed gauge data, coreAbsorb is the SHEAR
(T_1,...,T_L) ↦ (T_1 − shift_1, ..., T_L − shift_L) with shift_s = Z_s(I+X_s)⁻¹Y_s a function of the
spectator coords alone. A shear has Jacobian = I (det = 1) ⟹ MEASURE-PRESERVING. Verified numerically
(∂S_i/∂T_j = δ_ij). So coreAbsorb_rlct is TRIVIAL via rlctAtOn_comp_homeomorph (MP), no unit-peel needed.

The cert's "non-MP det(I−VY)⁻ᴹ⁰" was about the WRONG multiplicative-unit coreAbsorb (T·(I−VY)⁻¹, which
IS non-MP — det of a multiplicative matrix unit). The additive Schur shear is a different map.
</task>

<output_contract>
Terse:
1. Is coreAbsorb (the ADDITIVE per-layer Schur shear S_s = T_s − Z_s(I+X_s)⁻¹Y_s) MEASURE-PRESERVING?
   yes/no + the one-line reason. (Is my "shift_s independent of T_s ⟹ shear ⟹ det=1" correct, or is there
   a T_s-dependence I'm missing, e.g. through the FULL product Schur vs per-layer?)
2. Does coreAbsorb being MP make coreAbsorb_rlct TRIVIAL (rlctAtOn_comp_homeomorph, MP), dropping the
   weightedThreshold_weight_unit_invariant peel? Any catch (e.g. coreAbsorb MP on the core slot but the
   reg/spec interaction breaks global MP)?
3. THE CAVEAT: the squeeze core is ‖∏S_s‖² (product of the per-layer-sheared blocks). Does ∏S_s (per-layer
   Schur product) equal the loss core (= R|{E=0}, the FULL-product Schur)? Or do per-layer Schur and
   full-product Schur differ, breaking the squeeze target? (Earlier: for L=3 scalar, ∏S_s = R|{E=0} held.
   Does it hold for general L, matrix blocks? If not, the core object is ∏S_s OR R — which is the loss core?)
4. If coreAbsorb is MP: the cert + crux2's coreAbsorb_rlct field (built for a non-MP peel) are
   over-engineered. Is that a safe simplification (MP is STRICTLY easier — comp_homeomorph is proven), or
   does some downstream step actually NEED the non-MP machinery?
5. The most likely way the MP-shear claim is wrong.
</output_contract>

<grounding_rules>
The block algebra + S_s = T_s − Z(I+X)⁻¹Y (the #61-corrected core) are TRUSTED. Adjudicate the MP claim
+ the ∏S_s-vs-R caveat. Distinguish per-layer Schur (a shear, plausibly MP) from full-product Schur
(R = P11 − P10 P00⁻¹ P01, which depends on reg coords). Compute ∏S_s vs R for a 2-layer matrix case if
needed. If MP is right, confirm it's a strict simplification; if the squeeze needs R not ∏S_s, flag it.
