import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapse

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapseTall` — the `b=0` TALL front-Gram brick

**Thread `genm-lane1-shell` (Lane-1 front-collapse, the `b=0` tall wing).** The mirror of the wide
brick `front_gram_qbox_lt_top` (`RouteMSJFrontCollapse`) for a TALL front `F : M₀×M₁` (`M₁ ≤ M₀`,
full COLUMN rank `M₁`): the free-`F` COLUMN-Gram integral `∫_{F ∈ box} det(FᵀF)^{−M₂/2}` is finite
whenever `M₂ < M₀ − M₁ + 1` (the `b=0` bounded regime). This is the density factor the tall injective
front CoV produces (Jacobian reciprocal `det(FᵀF)^{−M₂/2}`, `FᵀF` the `M₁×M₁` column Gram, full rank).

The route is a pure transpose reduction to the LANDED wide brick: `det(FᵀF) = det(F̃·F̃ᵀ)` for the
transposed matrix `F̃ = Fᵀ` (`M₁×M₀`), and the measure-preserving transpose (`CorankSlabD.transp`)
carries the entry box `matBox M₀ M₁ 1` onto `matBox M₁ M₀ 1`, on which `front_gram_qbox_lt_top`
(with the roles of `M₀`, `M₁` swapped, `M₁ ≤ M₀`) closes it. No new Wishart primitive — the tall
Gram is the wide Gram of the transpose.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators Matrix

/-- **`Matrix.of (transp M₀ M₁ F) = (Matrix.of F)ᵀ`** — the measure-preserving transpose reindex is,
at the matrix level, the matrix transpose. -/
theorem of_transp_eq_transpose {M₀ M₁ : ℕ} (F : Fin M₀ → Fin M₁ → ℝ) :
    Matrix.of (CorankSlabD.transp M₀ M₁ F) = (Matrix.of F)ᵀ := by
  ext k i
  rfl

/-- **The tall column-Gram equals the wide row-Gram of the transpose.**
`det((of F)ᵀ · (of F)) = det((of (transp F)) · (of (transp F))ᵀ)`. -/
theorem det_colGram_eq_det_rowGram_transp {M₀ M₁ : ℕ} (F : Fin M₀ → Fin M₁ → ℝ) :
    ((Matrix.of F)ᵀ * (Matrix.of F)).det
      = ((Matrix.of (CorankSlabD.transp M₀ M₁ F)) * (Matrix.of (CorankSlabD.transp M₀ M₁ F))ᵀ).det := by
  rw [of_transp_eq_transpose, Matrix.transpose_transpose]

/-- **The transpose carries the tall entry box onto the wide entry box.**
`(transp M₀ M₁) ⁻¹' (matBox M₁ M₀ 1) = matBox M₀ M₁ 1`. -/
theorem transp_preimage_matBox {M₀ M₁ : ℕ} :
    (CorankSlabD.transp M₀ M₁) ⁻¹' (matBox M₁ M₀ 1) = matBox M₀ M₁ 1 := by
  ext F
  simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq, CorankSlabD.transp_apply]
  exact ⟨fun h i k => h k i, fun h k i => h i k⟩

/-- **The `b=0` TALL front-Gram qbox finiteness (the "first factor", `M₂ ≤ M₀ − M₁`).** The free-`F`
COLUMN Gram integral `∫_{F ∈ box} det(FᵀF)^{−M₂/2}` is finite whenever `M₁ ≤ M₀` (tall, full column
rank) and `M₂ < M₀ − M₁ + 1` (the `b=0` bounded regime). Transpose reduction to the wide brick
`front_gram_qbox_lt_top`: `det(FᵀF) = det(F̃·F̃ᵀ)` for `F̃ = Fᵀ`, and the measure-preserving
transpose carries `matBox M₀ M₁ 1` onto `matBox M₁ M₀ 1`. -/
theorem front_gram_qbox_tall_lt_top {M₀ M₁ : ℕ} (M₂ : ℕ) (hle : M₁ ≤ M₀)
    (hbnd : (M₂ : ℝ) < (M₀ : ℝ) - M₁ + 1) :
    (∫⁻ F in matBox M₀ M₁ 1,
        ENNReal.ofReal (((Matrix.of F)ᵀ * (Matrix.of F)).det ^ (-(M₂ : ℝ) / 2))) < ⊤ := by
  -- the integrand over the wide (transposed) matrix.
  set h : (Fin M₁ → Fin M₀ → ℝ) → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (((Matrix.of X) * (Matrix.of X)ᵀ).det ^ (-(M₂ : ℝ) / 2)) with hh
  -- the transpose change of variables.
  have hcov := (CorankSlabD.measurePreserving_transp M₀ M₁).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (CorankSlabD.transp M₀ M₁)) h (matBox M₁ M₀ 1)
  rw [transp_preimage_matBox] at hcov
  -- rewrite the goal's integrand to `h (transp F)`, land on the wide brick.
  have hgoal : (∫⁻ F in matBox M₀ M₁ 1,
        ENNReal.ofReal (((Matrix.of F)ᵀ * (Matrix.of F)).det ^ (-(M₂ : ℝ) / 2)))
      = ∫⁻ F in matBox M₀ M₁ 1, h (CorankSlabD.transp M₀ M₁ F) := by
    refine lintegral_congr fun F => ?_
    rw [hh, det_colGram_eq_det_rowGram_transp F]
  rw [hgoal, hcov]
  exact front_gram_qbox_lt_top (M₀ := M₁) (M₁ := M₀) M₂ hle hbnd

end DLNFibre.DLN.RLCT
