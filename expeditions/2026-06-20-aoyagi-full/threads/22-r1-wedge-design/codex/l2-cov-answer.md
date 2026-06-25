**1. Seam Choice**

Use **Seam 3, but factored**: define the chart on `Fin 21 → ℝ` explicitly as `schurShear334 ∘ pivotBlowupOn active334 p334`, and prove entry action by `equivFin` reflection lemmas. Do **not** compute the determinant of the composite Schur+blowup map as one flat fderiv. Factor the c-o-v: handle the Schur shear/reindexing as measure-preserving, and apply `perChart` only to the pure `pivotBlowupOn`, where `pivotBlowupOnDeriv_det` gives `u^7`.

**2. Shear As Separate Measure-Preserving Step**

Fact: yes, the shear is measure-preserving if the translated fiber coordinates `(E,y)` are shifted by a measurable function of the complementary coordinates `(a,b,c,S)` only. In product coordinates `(base, fiber)`, the map is `(b, z) ↦ (b, z + h b)`, and Mathlib has the right primitive: `MeasurePreserving.skew_product`; the fiber translation uses Haar invariance via `map_add_right_eq_self` / `map_add_left_eq_self`. For arbitrary coordinate subsets, split/reassemble with `volume_measurePreserving_sumPiEquivProdPi` and `volume_preserving_arrowCongr'`.

Inference: there is probably not a prepackaged “coordinate-subset shear” lemma with exactly this name; add a local `measurePreserving_coordShear` or directly prove `measurePreserving_schurShear334`. If `a⁻¹` is present, define the shift measurably across `a = 0` by an arbitrary branch; the fiberwise translation remains measure-preserving.

**3. Minimal Lemma Plan**

1. `coords334_reflect_and_active`  
   Define named flat coordinates for the relevant matrix entries; prove entry evaluation simps for `(paramsEquivFlat M334).symm`, `p334 ∈ active334`, and `active334.card = 8` using `equivFin` injectivity, not `decide`.

2. `measurePreserving_schurShear334`  
   `MeasurePreserving schurShear334 volume volume`; prove by coordinate split + `MeasurePreserving.skew_product` + translation invariance. No fderiv.

3. `schurPivot334_cov`  
   Factored c-o-v:
   `∫⁻` over `schurShear334 '' (pivotBlowupOn active334 p334 '' V)` equals the pullback integral with weight `ofReal (|u|^7)`. This is the only lemma carrying real fderiv weight, and it should only invoke existing `pivotBlowupOn_hasFDerivWithinAt`, `pivotBlowupOn_injOn`, `pivotBlowupOnDeriv_det`, and `coordZero_null`.

4. `schurPivot334_image_subset_cubeBox`  
   For every `ε > 0`, choose a chart box/slab `Vδ` whose image under `schurShear334 ∘ pivotBlowupOn active334 p334` lies in `cubeBox 21 ε`.

5. `routeMCore334_schurPivot_factor`  
   `routeMCore M334 (schurShear334 (pivotBlowupOn active334 p334 u)) = (u p334)^2 * Uval334 u`, using your banked `loss_schur_blowup_factor` plus the entry-reflection lemmas.

6. `leaf334_box_diverges`  
   Convert the post-c-o-v integrand to `monomialIntegrand 21 k334 h334 c' * Uval334 ^ (-c')`; use compact upper bound for `Uval334`, positivity from `Uval334_ge_sq` on the chosen positive box, and `monomialIntegrand_lintegral_box_eq_top` with `k p334 = 1`, `h p334 = 7`, threshold `4`.

7. `routeMCore334_cubeBox_diverges`  
   Assemble: image containment + `lintegral_mono_set` + `schurPivot334_cov` + factor identity + `leaf334_box_diverges`.

**4. One Honest Sorry If Needed**

If the factored route stalls, leave exactly this, not a composite determinant sorry:

```lean
theorem schurShear334_lintegral_image
    (S : Set (Fin 21 → ℝ)) (hS : MeasurableSet S)
    (g : (Fin 21 → ℝ) → ℝ≥0∞) :
    ∫⁻ x in schurShear334 '' S, g x ∂volume
      = ∫⁻ x in S, g (schurShear334 x) ∂volume := by
  sorry
```

That isolates the true shear measure-preservation obligation. Everything Jacobian-related should remain sorry-free through `pivotBlowupOn`.