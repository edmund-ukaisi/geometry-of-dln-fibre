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

/-- The all-zero parameter tuple has zero product (`L ≥ 1`: the recursion's last layer `= 0` zeroes
the fold). A public restatement of `Skeleton.prod_zero`. -/
theorem prod_zero_glue {L : ℕ} (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    prod M (0 : Params M) = 0 := by
  show prod M (fun _ => 0) = 0
  unfold prod
  obtain ⟨k, hk⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  subst hk
  rw [prodAux]; convert Matrix.mul_zero _

/-- **Region glue from the CoV bridge** (the analytic hole's discharge). Given a `ChartBridge` for `t`
and `c'` below half every terminal exponent, the unit-box layer-product integral is finite. `c' ≤ 0`:
the banked no-singularity corner. `L = 0`: `prod M A = 1` is constant, so the integrand is constant
on the compact box. `c' > 0, L ≥ 1`: `0` is in the zero-locus, contained in the atlas neighbourhood
`U`; a small box `paramsBoxM M ε ⊆ U ⊆ ⋃ leaves chartMap '' srcBox` bounds the box-`ε` integral by the
finite cover, then the homogeneity globalization lifts to the unit box. -/
theorem region_glue_of_chartBridge {L : ℕ} {M : Fin (L + 1) → ℕ} (t : ResolutionTree M)
    (hbridge : ChartBridge M t) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents t, c' < (e : ℝ) / 2) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  by_cases hc0 : c' ≤ 0
  · exact routeMLayerBoxIntegral_nonpos_lt_top M c' hc0
  have hcpos : 0 < c' := not_le.mp hc0
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · -- L = 0 : `prod M A` is the (constant) empty product
    subst hL0
    have hprodconst : ∀ A : Params M, prod M A = prod M (0 : Params M) := fun A => rfl
    rw [routeMLayerBoxIntegral,
      setLIntegral_congr_fun (measurableSet_paramsBoxM M 1) (fun A _ => by rw [hprodconst A]),
      setLIntegral_const]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have hcubeM : MeasurableSet (cubeBox (flatDim M) 1) := by
      rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
    rw [← paramsEquivFlat_preimage_paramsBoxM M 1,
      (measurePreserving_paramsEquivFlat M).measure_preimage hcubeM.nullMeasurableSet]
    exact (show IsCompact (cubeBox (flatDim M) 1) by
      rw [cubeBox]; exact isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top
  · -- c' > 0, L ≥ 1
    -- Flat virtual-leaf atlas: the atlas + (A) cover, (B) per-piece props, (C) exponents.
    -- Clause (A) now delivers `0 ∈ U` directly (the consumer-honest form); the origin is the
    -- singularity that `routeMLayerBoxIntegral_lt_top_of_small_box`'s scale-homogeneity reduces to.
    obtain ⟨atlas, ⟨U, hUopen, hUlocus, hUcover⟩, hleaf, hexp⟩ := hbridge
    obtain ⟨ε, hε, hεU⟩ := exists_small_paramsBox_subset_open hUopen hUlocus
    -- Each atlas piece has finite chart-image integral; the thresholds route through clause (C).
    have Hleaf : ∀ c ∈ atlas, ∫⁻ A in c.chartMap '' c.srcBox,
        ENNReal.ofReal (frobSq (prod M A) ^ (-c')) < ⊤ := by
      intro c hc
      obtain ⟨hsrcM, hbdd, hdcInj, hrcInj, hdisj, hnull, hlp, hlj⟩ := hleaf c hc
      obtain ⟨hdivmem, hresmem⟩ := hexp c hc
      exact leaf_chart_image_lintegral_lt_top c c' hcpos hsrcM hbdd hdcInj hrcInj hdisj hnull hlp
        hlj (fun k => hrat _ (hdivmem k)) (fun hpos => hrat _ (hresmem hpos))
    refine routeMLayerBoxIntegral_lt_top_of_small_box M c' ε hε ?_
    rw [routeMLayerBoxIntegral]
    exact lt_of_le_of_lt (lintegral_mono_set (hεU.trans hUcover))
      (lintegral_leaves_cover_lt_top c' atlas Hleaf)

end DLNFibre.DLN.RLCT.Engine
