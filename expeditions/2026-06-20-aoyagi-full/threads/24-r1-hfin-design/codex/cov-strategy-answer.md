I checked the local Mathlib v4.29 sources; lemma names below are verified unless marked otherwise.

**Ranked Verdict**

1. **B, but only with structural det factorisation.** Build `paramsEquivFlat` as a `LinearEquiv`/`ContinuousLinearEquiv`, then prove the derivative of `phi334` through it. This matches Mathlib: `LinearEquiv.piCurry`, `LinearEquiv.funCongrLeft`, `LinearEquiv.toContinuousLinearEquiv`, `ContinuousLinearMap.hasFDerivAt`, `HasFDerivAt.comp_hasFDerivWithinAt`, and the target `lintegral_image_eq_lintegral_abs_det_fderiv_mul`. For determinants, use `LinearMap.det_comp`, `LinearMap.det_conj`, `pivotBlowupOnDeriv_det`, `LinearMap.transvection.det`, and `Matrix.abs_det_reindex`/`Matrix.abs_det_submatrix_equiv_equiv`. Biggest risk: if you try to compute `D(chartParams334)` as a raw 21×21 determinant, you lose; you need the pivot/blow-up/shear factorisation.

2. **A is not type-dead, but the naive peel is.** Pure peeling gives an integral over `chartParams334 '' s`, but Mathlib’s Jacobian theorem is for `f : E → E`, not `Flat → Params`. The clean self-map reduction is on parameter space: with `E = paramsEquivFlat M334`, use `h := chartParams334 ∘ E : Params M334 → Params M334` and source `E.symm '' s`; then transport integrals by `MeasurePreserving.setLIntegral_comp_emb` and apply Jacobian to `h`. This still needs the linear/CLE version of `E` and the determinant of `D chart ∘ E`, so it adds measure/set plumbing without removing the real blocker.

3. **C is mathematically clean but highest-risk in this repo.** A flat `psiFlat` built from `pivotBlowupOn` plus shears would reuse the `(2,2,2)` pattern directly: `pivotBlowupOn_hasFDerivWithinAt`, `pivotBlowupOn_injOn`, `pivotBlowupOnDeriv_det`, plus det-one shears. The risk is the agreement proof with `phi334`, because `paramsEquivFlat` contains the opaque `Fintype.equivFin (FlatIdx M334)` reindex. Re-proving the loss bridge for `psiFlat` likely hits the same wall.

**Winning Route Steps**

1. Define `paramsEquivFlatLinear H : Params H ≃ₗ[ℝ] (Fin (flatDim H) → ℝ)` using two `LinearEquiv.piCurry` steps and final `LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (FlatIdx H)).symm`.

2. Package `paramsEquivFlatCLE H := (paramsEquivFlatLinear H).toContinuousLinearEquiv`; prove apply/symm apply lemmas matching `paramsEquivFlat H` by `funext`/`simp`.

3. Prove fderiv lemmas for the flattening:
`HasFDerivAt (paramsEquivFlat H) (paramsEquivFlatCLE H : _ →L[ℝ] _) A`, via `ContinuousLinearMap.hasFDerivAt` plus congruence.

4. Work first on the good set
`V \ ({u | u 0 = 0} ∪ {u | u 1 = 0})`, where `phi334_injOn` applies.

5. Define `D334 u` structurally, not by expanding `chartParams334`: pivot-0 derivative, `b = aβ` as another `pivotBlowupOn` on `{1,2,3}` with pivot `1`, and shear derivatives as transvections.

6. Prove
`HasFDerivWithinAt phi334 (D334 u) goodSet u`
by chain rule: `HasFDerivWithinAt.comp`, `HasFDerivAt.comp_hasFDerivWithinAt`, `HasFDerivWithinAt.congr`.

7. Prove
`|(D334 u).det| = |u 0|^7 * |u 1|^2`
using `pivotBlowupOnDeriv_det` twice, `LinearMap.transvection.det` / `LinearEquiv.transvection.det_eq_one` for shears, `LinearMap.det_comp`, and `Matrix.abs_det_reindex` for the coordinate reindex. No symbolic 21×21 determinant.

8. Apply `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, then add back `{u | u 1 = 0}`: RHS is killed by the `|u 1|^2` factor; LHS image is null using `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` plus `coordZero_null 1`.

**Q3 Shortcut**

Yes for the reindex, but not from `measurePreserving_paramsEquivFlat` directly. Use the matrix permutation lemmas:

- `Matrix.abs_det_reindex`
- `Matrix.abs_det_submatrix_equiv_equiv`

I did not find a direct v4.29 lemma “measure-preserving linear equiv implies abs det = 1”. For endomorphisms, the relevant Haar scaling theorem is `map_linearMap_addHaar_eq_smul_addHaar`, but turning that into a determinant rewrite is extra work and not the shortest path.

**Effort Estimate**

Not a ≤200-line one-day close. This is the flagged multi-file infrastructure build: about **500–800 lines across 2 files**, roughly **2–4 focused days**.

Smallest honest bankable partial: add `paramsEquivFlatLinear`, `paramsEquivFlatCLE`, apply/symm lemmas, and `HasFDerivAt`/`HasFDerivWithinAt` lemmas for `paramsEquivFlat`. That is worth banking on its own: **80–140 lines in `ParamsFlat.lean`**. The wall after that is exactly the structural `D334_det_abs` proof and the `{u1 = 0}` null-slice reinsertion.