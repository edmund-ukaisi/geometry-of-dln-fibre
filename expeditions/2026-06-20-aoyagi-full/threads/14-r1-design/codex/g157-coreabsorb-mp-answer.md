1. **Yes.** The additive per-layer map `T_s ↦ T_s - Z_s(I+X_s)⁻¹Y_s` is triangular in `(T_s, X_s,Y_s,Z_s)` with identity on the `T_s` diagonal, so Jacobian determinant is `1`.

2. **Yes, for that map.** If `coreAbsorb` fixes reg/spec and only shears raw `T` to per-layer `S`, then `coreAbsorb_rlct` is the MP homeomorphism transport. No reg/spec catch under the stated split.

3. **No in general.** The loss core is the **full-product Schur** `R = P11 - P10 P00⁻¹ P01`, not naïvely `∏S_s`. For two layers,
   `Schur(C₁C₂) = S₁ (I + G E⁻¹ A⁻¹ B)⁻¹ S₂`
   in block notation, so an interstitial unit remains. Thus `∏S_s = R|{E=0}` is a scalar/special-case accident, not a general matrix identity.

4. **Safe simplification only for the additive shear.** Drop the unit-weight peel for `T ↦ T - Z(I+X)⁻¹Y`. But downstream may still need non-MP/unit machinery to absorb the inter-layer units converting the full-product Schur core `R` into a standard reduced-chain product.

5. **Most likely failure mode:** not hidden `T_s`-dependence. The MP shear claim is right. The danger is identifying the per-layer Schur product `∏S_s` with the full-product loss core `R`.