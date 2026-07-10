import DLNFibre.DLN.RLCT.Validate.RouteMSJVExpose

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJPivotTranslate` — the pivot-row translation (v-exposure atom)

**Thread `genm-covmount`, Stage 2 (S,J) CoV mountain, transport step (c).** The `v`-exposure
change-of-variables (route A, decorrelated-Codex-confirmed) turns the pivot rows of the front factor
into the free boundary variable `v` by a translation. This module banks that atom: the pivot-row
integral over its box equals the boundary integral over the translated (shifted) box, with the front
factor reconstructed by `assembleFront` (`RouteMSJVExpose`).

* **`sjGoodChartLoss_pivotRows_translate_eq`** — the translation EQUALITY: for a fixed corank map
  `W`: `∫_{U ∈ matBox} (sjGoodChartLoss x Γ (of (Sum.elim U W)) A₂)^{−c'}` (pivot rows `U` free)
  equals `∫_{v ∈ {v | v − P⁻¹B₁₂W ∈ matBox}} (sjGoodChartLoss x Γ (assembleFront x v W) A₂)^{−c'}`
  (boundary rows `v` over the shear-image box). The map `U ↦ v = U + P⁻¹B₁₂W` is a translation
  (`measurePreserving_add_right`); `assembleFront x v W = of (Sum.elim (v − P⁻¹B₁₂W) W)` makes the
  substituted integrand definitionally the reconstruction.

The composition consuming this (step 1 of the transport, route A per the Codex design
`codex/transport-answer.md`): the `A' 0`-vs-deeper Pi-split (`eFront`/`piFinSuccAbove`) + the
`A' 0` row-reindex/split into pivot-rows × corank-rows(=W) (`blockSplitD`/`splitCols`), THEN this
translation. The shifted `v`-box then feeds the BALL endpoint (`corner_block_lt_top_of_pos` +
shifted-box ⊆ fixed-ball domination) for the environment integration.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (a measure-preserving translation + defeq).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal

variable {t a b h o : ℕ}

/-- **The pivot-row translation (the `v`-exposure atom).** For a fixed corank map `W`, the pivot-row
integral over its box equals the boundary integral over the shear-image box: `U ↦ v = U + P⁻¹B₁₂W`
is a measure-preserving translation, and `assembleFront x v W = of (Sum.elim (v − P⁻¹B₁₂W) W)` makes
the substituted integrand the reconstruction. Transport `∫_{U ∈ box}` along the MP translation
(`measurePreserving_add_right`, `setLIntegral_comp_preimage_emb`); the domain becomes the
preimage `{v | v − P⁻¹·B₁₂·W ∈ box}` and the integrand `assembleFront` by defeq. -/
theorem sjGoodChartLoss_pivotRows_translate_eq
    (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ)
    (W : Matrix (Fin b) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ) (c' : ℝ) :
    (∫⁻ U in matBox t h 1,
        ENNReal.ofReal ((sjGoodChartLoss x Γ (Matrix.of (Sum.elim U W)) A2) ^ (-c')))
      = ∫⁻ v in {v : Matrix (Fin t) (Fin h) ℝ |
          v - (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * W ∈ matBox t h 1},
          ENNReal.ofReal ((sjGoodChartLoss x Γ (assembleFront x v W) A2) ^ (-c')) := by
  have hmp := (measurePreserving_add_right (volume : Measure (Fin t → Fin h → ℝ))
      (-((Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * W))).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight _)
    (fun U : Fin t → Fin h → ℝ =>
      ENNReal.ofReal ((sjGoodChartLoss x Γ (Matrix.of (Sum.elim U W)) A2) ^ (-c')))
    (matBox t h 1)
  rw [← hmp]
  rfl

end DLNFibre.DLN.RLCT
