import DLNFibre.Core.Aoyagi.Waypoint
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# `Core.Aoyagi.AreaFormula` — the InjOn-off-null area formula (Object B's CoV substrate)

The change-of-variables / area formula that Object B's atlas rides. Mathlib's equality forms
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul` &c., pinned as contracts in
`Core.Aoyagi.Waypoint`) require the map to be `InjOn` on **all** of the source set. A resolution
chart is only **a.e.-injective** — injective off a null exceptional locus `excep` (the birational
content). This module supplies the **InjOn-off-null relaxation**: the area-formula `lintegral`
equality continues to hold when injectivity is dropped on a null set, because

* the image `g '' s` and `g '' (s \ excep)` differ only by `g '' (s ∩ excep) ⊆ g '' excep`, which is
  null (a differentiable map sends a null set to a null set,
  `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`); and
* `s` and `s \ excep` differ only by the null `s ∩ excep`.

So both integrals are unchanged by deleting the null branch set, where Mathlib's on-the-nose
equality applies. This is the *named remainder* Object B's chart lane owed
(`Core.Aoyagi.Waypoint`, remainder (b)); it serves **both** legs of the atlas change-of-variables
(the per-chart `≤` and the atlas-min `≥` — the latter via ENNReal subadditivity over the finite
covering union, each term being a single-chart equality here).
-/

open MeasureTheory Set
open scoped ENNReal

namespace DLNFibre.Core.Aoyagi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The InjOn-off-null area formula (lintegral form).** For a globally differentiable `g` that is
injective on `s \ excep` with `excep` a null measurable set, the area-formula `lintegral` equality
`∫⁻_{g '' s} h = ∫⁻_s |det Dg| · (h ∘ g)` holds — the a.e.-injective relaxation of
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`. The exceptional (non-injective) locus is deleted
on both sides: its image is null (differentiable image of a null set) and `s ∩ excep` is null. -/
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul_of_injOn_off_null
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {g : E → E} {s excep : Set E}
    (hs : MeasurableSet s) (hgdiff : Differentiable ℝ g)
    (hexcep_meas : MeasurableSet excep) (hexcep_null : μ excep = 0)
    (hinj : InjOn g (s \ excep)) (h : E → ℝ≥0∞) :
    ∫⁻ x in g '' s, h x ∂μ
      = ∫⁻ u in s, ENNReal.ofReal |(fderiv ℝ g u).det| * h (g u) ∂μ := by
  -- `s \ excep` is measurable, and `g` has its `fderiv` as a `HasFDerivWithinAt` derivative there.
  have hse : MeasurableSet (s \ excep) := hs.diff hexcep_meas
  have hf' : ∀ u ∈ s \ excep, HasFDerivWithinAt g (fderiv ℝ g u) (s \ excep) u :=
    fun u _ ↦ (hgdiff u).hasFDerivAt.hasFDerivWithinAt
  -- Mathlib's on-the-nose equality on the injective part.
  have eq1 : ∫⁻ x in g '' (s \ excep), h x ∂μ
      = ∫⁻ u in s \ excep, ENNReal.ofReal |(fderiv ℝ g u).det| * h (g u) ∂μ :=
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hse hf' hinj h
  -- `g '' (s ∩ excep) ⊆ g '' excep` is null (differentiable image of a null set).
  have himg_null : μ (g '' excep) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      μ (hgdiff.differentiableOn) hexcep_null
  -- LHS: `g '' s =ᵐ g '' (s \ excep)` (differ inside the null `g '' excep`).
  have hLHS : ∫⁻ x in g '' s, h x ∂μ = ∫⁻ x in g '' (s \ excep), h x ∂μ := by
    refine setLIntegral_congr ?_
    rw [ae_eq_set]
    constructor
    · -- `g '' s \ g '' (s \ excep) ⊆ g '' excep`
      refine measure_mono_null (fun y hy ↦ ?_) himg_null
      obtain ⟨⟨u, hus, rfl⟩, hy2⟩ := hy
      by_cases hu : u ∈ excep
      · exact ⟨u, hu, rfl⟩
      · exact absurd ⟨u, ⟨hus, hu⟩, rfl⟩ hy2
    · -- `g '' (s \ excep) \ g '' s = ∅` since `s \ excep ⊆ s`
      refine measure_mono_null (fun y hy ↦ ?_) (measure_empty (μ := μ))
      exact absurd (Set.image_mono Set.diff_subset hy.1) hy.2
  -- RHS: `s \ excep =ᵐ s` (differ inside the null `excep`).
  have hRHS : ∫⁻ u in s \ excep, ENNReal.ofReal |(fderiv ℝ g u).det| * h (g u) ∂μ
      = ∫⁻ u in s, ENNReal.ofReal |(fderiv ℝ g u).det| * h (g u) ∂μ := by
    refine setLIntegral_congr ?_
    rw [ae_eq_set]
    refine ⟨measure_mono_null (fun y hy ↦ absurd (Set.diff_subset hy.1) hy.2)
        (measure_empty (μ := μ)),
      measure_mono_null (fun y hy ↦ ?_) hexcep_null⟩
    by_contra hne
    exact hy.2 ⟨hy.1, hne⟩
  rw [hLHS, eq1, hRHS]

end DLNFibre.Core.Aoyagi
