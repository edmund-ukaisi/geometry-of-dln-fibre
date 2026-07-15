import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option linter.style.longLine false

/-!
# `RouteMSJIncidenceGluing` — Brick D piece (iii): the generic finite-atlas gluing core

**Thread `genm-sj5-brickdcont`.** The atlas-independent gluing logic for the incidence resolution
(`incidence-cert.md` §3b, "null-overlap gluing"): a finite family of measurable cells covering the domain
up to a null set, each with finite lower integral, glues to a finite domain integral.

This is **PARAMETERIZED on the atlas** — the cells `C` and the up-to-null coverage are HYPOTHESES, not
built here. So it is **robust to any `genm-bltj` verdict**: bltj can only reshape WHICH charts appear or
WHETHER they cover (an extra `b < j` cell, a different coverage proof) — i.e. the hypotheses `C`/`hcover` —
never this gluing logic. The atlas-SPECIFIC union (which cells, that they cover) is deliberately NOT built
here; it is supplied by the caller once bltj fixes the atlas. Network-free measure theory; axiom-clean.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal

/-- **Generic finite-atlas gluing core.** If a `Fintype`-indexed family of cells `C : ι → Set α` covers the
domain `D` up to a null set (`μ (D \ ⋃ i, C i) = 0`) and each cell has finite lower integral of `f`, then the
domain integral `∫⁻_D f` is finite. Atlas-parameterized (cells + coverage as hypotheses) — the gluing logic
is independent of the specific chart geometry. -/
theorem lintegral_lt_top_of_finite_cover {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Fintype ι] (C : ι → Set α) (D : Set α) (f : α → ℝ≥0∞)
    (hcover : μ (D \ ⋃ i, C i) = 0)
    (hfin : ∀ i, ∫⁻ x in C i, f x ∂μ < ⊤) :
    ∫⁻ x in D, f x ∂μ < ⊤ := by
  calc ∫⁻ x in D, f x ∂μ
      ≤ ∫⁻ x in ⋃ i, C i, f x ∂μ := lintegral_mono_set' (ae_le_set.mpr hcover)
    _ ≤ ∑' i, ∫⁻ x in C i, f x ∂μ := lintegral_iUnion_le C f
    _ = ∑ i, ∫⁻ x in C i, f x ∂μ := tsum_fintype _
    _ < ⊤ := ENNReal.sum_lt_top.mpr (fun i _ => hfin i)

/-- **Finset-atlas variant.** The `Finset`-indexed form (charts indexed by a finite set of minors): cells
`C i` for `i ∈ s` covering `D` up to null, each with finite integral ⟹ `∫⁻_D f < ⊤`. Reduces to the
`Fintype` core over the subtype `↥s`. -/
theorem lintegral_lt_top_of_finset_cover {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (C : ι → Set α) (D : Set α) (f : α → ℝ≥0∞)
    (hcover : μ (D \ ⋃ i ∈ s, C i) = 0)
    (hfin : ∀ i ∈ s, ∫⁻ x in C i, f x ∂μ < ⊤) :
    ∫⁻ x in D, f x ∂μ < ⊤ := by
  refine lintegral_lt_top_of_finite_cover (fun i : (s : Set ι) => C (i : ι)) D f ?_
    (fun i => hfin (i : ι) (Finset.mem_coe.mp i.2))
  have hunion : ⋃ i : (s : Set ι), C (i : ι) = ⋃ i ∈ s, C i := by
    rw [Set.iUnion_coe_set]; simp
  rw [hunion]; exact hcover

end DLNFibre.DLN.RLCT
