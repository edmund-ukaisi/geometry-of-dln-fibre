import DLNFibre.Core.Aoyagi.IdealInvariance
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet

/-!
# `Core.Aoyagi.Waypoint` — shared discharge helpers for Object A's guards + the CoV surface

This module collects the *shared waypoint helpers* consumed downstream of Object A
(`Core.Aoyagi.IdealInvariance`): the honest at-use-site discharge of the `LocallyNullZeros` junk-`0`
guard for the DLN/polynomial case, and a pinned catalogue of the Mathlib change-of-variables / area
formula that Object B's charts ride.

## (i) Discharging `LocallyNullZeros` for a polynomial generator

The Object A leaves carry `LocallyNullZeros (sumSqFam G) x` as a hypothesis (the junk-`0` guard).
For the DLN case the generators `Gᵢ` are matrix-product *entries* — evaluations of real polynomials
— so the guard is discharged, at every point and globally, by the existing Core primitive
`MvPolynomial.volume_zeroSet_eq_zero` (a nonzero real polynomial vanishes on a `volume`-null set):
`{∑ Gⱼ² = 0} ⊆ {Gᵢ = 0} = {eval · P = 0}` is null whenever *one* generator is a nonzero polynomial.
So the guard is dischargeable, not a hidden hypothesis — as the leaf docstrings promised.

## (iii) The change-of-variables / area-formula surface (Mathlib v4.29)

Mathlib provides, for a function `f` injective and differentiable on a measurable set `s`, the
**equality** forms of the area formula (below, pinned as `example` contracts so a Mathlib rename is
caught here):

* `lintegral_image_eq_lintegral_abs_det_fderiv_mul` — `∫⁻_{f''s} g = ∫⁻_s |det f'|·(g∘f)`;
* `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` — the integrability transfer;
* `integral_image_eq_integral_abs_det_fderiv_smul` — the Bochner equality.

and, WITHOUT injectivity, the **subadditive measure bound**
`addHaar_image_le_lintegral_abs_det_fderiv` : `μ (f '' s) ≤ ∫⁻_s |det f'|`.

**Named remainder (owned by Object B's chart lane, not built here).** Two relaxations the B charts
may need are *not* in these lemmas and are deliberately left to the consuming lane, where the exact
form is known: (a) the **weighted non-injective subadditive** integral bound
`∫⁻_{f''s} g ≤ ∫⁻_s |det f'|·(g∘f)` for a general `g` (Mathlib's non-injective `≤` is measure-only,
the `g ≡ 1` case); (b) the **InjOn-off-null** relaxation of the equality forms (Mathlib requires
`InjOn f s` on all of `s`; an a.e.-injective refinement restricts to `s` minus the null branch set
and absorbs the null image difference). Building a speculative wrapper for an unspecified consumer
risks a wrong statement, so the reachable deliverable here is the verified catalogue + this boundary.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DLNFibre.Core.Aoyagi

variable {n : ℕ}

/-! ## (i) `LocallyNullZeros` discharge for a polynomial generator -/

/-- The sum-of-squares zero set sits inside each generator's zero set: if `∑ⱼ (Gⱼ w)² = 0` then, the
summands being nonnegative, every `(Gⱼ w)² = 0`, in particular `Gᵢ w = 0`. -/
lemma sumSqFam_zeroSet_subset {p : ℕ} (G : Fin p → (Fin n → ℝ) → ℝ) (i : Fin p) :
    {w : Fin n → ℝ | sumSqFam G w = 0} ⊆ {w | G i w = 0} := by
  intro w hw
  simp only [sumSqFam, Set.mem_setOf_eq] at hw ⊢
  have hsq : (G i w) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg (G j w)).1 hw i (Finset.mem_univ i)
  exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 hsq

/-- **Discharging `LocallyNullZeros` for a polynomial generator.** If one generator `Gᵢ` equals the
evaluation of a NONZERO real polynomial `P`, then the sum-of-squares zero set `{∑ Gⱼ² = 0}` is
`volume`-null — it sits inside `{eval · P = 0}`, null by `MvPolynomial.volume_zeroSet_eq_zero` — so
`LocallyNullZeros (sumSqFam G) x` holds at every `x` (with the neighbourhood `Set.univ`). The honest
at-use-site discharge of Object A's junk-`0` guard for the DLN/polynomial case. -/
theorem locallyNullZeros_sumSqFam_of_polynomial {p : ℕ} {G : Fin p → (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} (i : Fin p) (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0)
    (hGi : ∀ w, G i w = MvPolynomial.eval w P) :
    LocallyNullZeros (sumSqFam G) x := by
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  rw [Set.inter_univ]
  refine measure_mono_null (sumSqFam_zeroSet_subset G i) ?_
  have hset : {w : Fin n → ℝ | G i w = 0} = {w | MvPolynomial.eval w P = 0} := by
    ext w; simp only [Set.mem_setOf_eq, hGi w]
  rw [hset]
  exact MvPolynomial.volume_zeroSet_eq_zero P hP

/-! ## (iii) Pinned Mathlib area-formula contracts (durable, elaboration-checked) -/

section AreaFormula

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}

/-- Contract: the `lintegral` area-formula equality under `InjOn f s`. -/
example (μ : Measure E) [μ.IsAddHaarMeasure] (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ :=
  lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hf' hf g

/-- Contract: the integrability transfer under `InjOn f s`. -/
example (μ : Measure E) [μ.IsAddHaarMeasure] (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → F) :
    IntegrableOn g (f '' s) μ ↔ IntegrableOn (fun x ↦ |(f' x).det| • g (f x)) s μ :=
  integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hf' hf g

/-- Contract: the Bochner area-formula equality under `InjOn f s`. -/
example (μ : Measure E) [μ.IsAddHaarMeasure] (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ :=
  integral_image_eq_integral_abs_det_fderiv_smul μ hs hf' hf g

/-- Contract: the subadditive measure bound WITHOUT injectivity (the `g ≡ 1` non-injective case). -/
example (μ : Measure E) [μ.IsAddHaarMeasure] (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    μ (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ :=
  addHaar_image_le_lintegral_abs_det_fderiv μ hs hf'

end AreaFormula

end DLNFibre.Core.Aoyagi
