import DLNFibre.DLN.RLCT.Engine.RegionGluePerLeaf
import DLNFibre.DLN.RLCT.Engine.RegionGlueGlobalize

/-!
# `DLNFibre.DLN.RLCT.Engine.RegionGlueAssembly` — the `region_glue` cover assembly

Glues the per-leaf area-formula read (`RegionGluePerLeaf`) and the homogeneity local→global step
(`RegionGlueGlobalize`) into the full `region_glue` discharge from a `ChartBridge`:

    `region_glue_of_chartBridge` : `ChartBridge M t → (∀ e ∈ terminalExponents t, c' < e/2) →
      routeMLayerBoxIntegral M c' 1 < ⊤`.

Route (`c' > 0`, `L ≥ 1`): `0` lies in the zero-locus (`prod M 0 = 0`), which the atlas neighbourhood
`U` contains; a small box `paramsBoxM M ε ⊆ U ⊆ ⋃ leaves chartMap '' srcBox`
(`exists_small_paramsBox_subset_open`), so the box-`ε` integral is `≤` the finite-leaves cover integral
(`lintegral_leaves_cover_lt_top`, each leaf finite by `leaf_chart_image_lintegral_lt_top`); the
scaling-bridge globalization lifts finiteness to the unit box. `c' ≤ 0` is the banked no-singularity
corner; `L = 0` has a constant integrand (`prod M A = 1`).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **A small parameter box sits inside any open neighbourhood of `0`.** `paramsBoxM M ε ⊆ U` for some
`ε > 0`: pull `U` back through the continuous linear `paramsEquivFlatCLE.symm` to a flat open
neighbourhood of `0`, take a flat cube inside it (`cubeBox_subset_of_isOpen`), and push back via
`paramsEquivFlat_preimage_paramsBoxM`. -/
theorem exists_small_paramsBox_subset_open {M : Fin (L + 1) → ℕ} {U : Set (Params M)}
    (hU : IsOpen U) (h0 : (0 : Params M) ∈ U) : ∃ ε > 0, paramsBoxM M ε ⊆ U := by
  have hVopen : IsOpen ((paramsEquivFlatCLE M).symm ⁻¹' U) :=
    hU.preimage (paramsEquivFlatCLE M).symm.continuous
  have h0V : (0 : Fin (flatDim M) → ℝ) ∈ (paramsEquivFlatCLE M).symm ⁻¹' U := by
    simp only [Set.mem_preimage, map_zero]; exact h0
  obtain ⟨ε, hε, hεsub⟩ := cubeBox_subset_of_isOpen hVopen h0V
  refine ⟨ε, hε, fun A hA => ?_⟩
  rw [← paramsEquivFlat_preimage_paramsBoxM M ε, Set.mem_preimage] at hA
  have hmem := hεsub hA
  rw [Set.mem_preimage] at hmem
  have hcoe : (paramsEquivFlatCLE M).symm (paramsEquivFlat M A) = A := by
    rw [← paramsEquivFlatCLE_coe]; exact (paramsEquivFlatCLE M).symm_apply_apply A
  rwa [hcoe] at hmem

/-- **Finiteness over a finite leaf cover.** If the box integral is finite over each leaf's chart
image, it is finite over their union — a `List` induction on `lintegral_union_le`. -/
theorem lintegral_leaves_cover_lt_top {M : Fin (L + 1) → ℕ} (c' : ℝ) (ls : List (LeafData M))
    (H : ∀ l ∈ ls, ∫⁻ A in l.chartMap '' l.srcBox,
      ENNReal.ofReal (frobSq (prod M A) ^ (-c')) < ⊤) :
    ∫⁻ A in ⋃ l ∈ ls, l.chartMap '' l.srcBox,
      ENNReal.ofReal (frobSq (prod M A) ^ (-c')) < ⊤ := by
  induction ls with
  | nil => simp
  | cons l₀ rest ih =>
      have hsplit : (⋃ l ∈ (l₀ :: rest), l.chartMap '' l.srcBox)
          = l₀.chartMap '' l₀.srcBox ∪ ⋃ l ∈ rest, l.chartMap '' l.srcBox := by
        simp only [List.mem_cons, Set.iUnion_or, Set.iUnion_union_distrib,
          Set.iUnion_iUnion_eq_left]
      rw [hsplit]
      exact lt_of_le_of_lt (lintegral_union_le _ _ _)
        (ENNReal.add_lt_top.mpr ⟨H l₀ (List.mem_cons.mpr (Or.inl rfl)),
          ih (fun l hl => H l (List.mem_cons.mpr (Or.inr hl)))⟩)

end DLNFibre.DLN.RLCT.Engine
