1. **B1 wins**: `Matrix.Vec` already has `Matrix.kronecker_mulVec_vec`, so the main vec identity is a fact, not a new proof; determinant lift is just `Matrix.det_kronecker` + `simp`.
2. **B2 second**: avoids determinant, but still needs generator/product bookkeeping for left/right multiplication on `vec A`.
3. **A third**: green atoms exist, but the general finite shear composition and flattening/order bookkeeping are the most indexing-heavy.

**Winner Chain**

Fact, checked locally:

1. State a reusable lemma with finite row/column types:
   `MeasurePreserving (fun A : Matrix ρ κ ℝ => L * A * R)` assuming `hL : L.det = 1`, `hR : R.det = 1`.

2. Add one local glue equivalence, not Mathlib: “`Matrix.vec` as a measure-preserving measurable equivalence”
   `Matrix ρ κ ℝ ≃ᵐ (κ × ρ → ℝ)`.
   Build it from `MeasurableEquiv.curry`, `volume_measurePreserving_piCongrLeft`, possibly `volume_preserving_arrowCongr'`.

3. Under `vec`, identify the map:
   `Matrix.kronecker_mulVec_vec L A Rᵀ` + `Matrix.toLin'_apply` + `transpose_transpose` gives
   `vec (L * A * R) = Matrix.toLin' (Rᵀ ⊗ₖ L) (vec A)`.

4. Compute determinant:
   `Matrix.det_kronecker`, `Matrix.det_transpose`, `hL`, `hR` give
   `det (Rᵀ ⊗ₖ L) = 1`.

5. Apply
   `Real.map_matrix_volume_pi_eq_smul_volume_pi`
   to `Rᵀ ⊗ₖ L`; rewrite `|1|⁻¹ = 1`, hence `Measure.map ... volume = volume`, and transport back across the `vec` equivalence using `MeasurePreserving.comp`.

For the block-unipotent Schur instance, discharge `hL`, `hR` separately using `Matrix.det_fromBlocks_zero₁₂` / `Matrix.det_fromBlocks_zero₂₁` and `det_one`.

**Risk**

Biggest risk: the local `vec` measurable-equivalence wrapper orientation. Cheapest de-risk: first prove the theorem for `ρ = Fin 2`, `κ = Fin 3` with arbitrary det-1 `L,R`, before touching block `Fin (m+l)` / `Fin (m+n)`.

**Statement Shape**

State (3) on `Matrix ρ κ ℝ` with finite index types and det-1 hypotheses; add a flattened corollary only for the eventual `χ : Fin N → ℝ` interface.