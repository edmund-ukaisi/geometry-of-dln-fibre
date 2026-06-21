import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1G5` — the change-of-variables cover-gluing lemma (G5-abstract)

R1's resolution expresses a threshold integral `∫⁻_U g` (here `g = |F|^{−c}`, an `ℝ≥0∞`-valued
integrand — `lintegral` so no integrability side-conditions, the `∞`-above-the-rlct value handled
unconditionally) as a sum over the leaves of a finite chart cover:
`∫⁻_U g = Σ_leaves ∫⁻_{V_i} (g∘φ_i)·|Jac φ_i|`. This file builds the **flat-cover** form (one cover
level), the G5-instance the explicit `(2,2,2)` 24-leaf cover uses directly; the multi-level blow-up
tree is this composed across levels (caller-side).

## The pieces (all Mathlib facts, checked)
- **Single change-of-variables** (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`):
  `∫⁻ x in φ '' s, g x = ∫⁻ x in s, ofReal |det (φ' x)| · g (φ x)` for `φ` C¹ + `InjOn` on the
  measurable `s`. Over `ℝ≥0∞` ⟹ no integrability hypotheses.
- **Null-exceptional adapter** (`perChart`): blow-up charts are `InjOn` only off the exceptional
  locus `N` (a null set). Apply the c-o-v on `V \ N` (where `φ` is injective) and drop `N` from the
  image (`φ '' N` null ⟹ `∫⁻_{φ''(V\N)} = ∫⁻_{φ''V}`).
- **Cover-additivity** (`lintegral_biUnion_finset₀`): `∫⁻` over an a.e.-disjoint finite cover is the
  sum.

The per-node hypotheses (C¹, `InjOn`-off-null, `φ''N` null, a.e.-disjoint null-cover) are
**discharged by the caller** (R1's explicit polynomial blow-up charts) — so this lemma isolates
the measure-theory from the quiver-geometry (G3). -/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- **Per-chart change-of-variables with the null-exceptional drop.** For a chart `φ` that is C¹ and
injective on `V \ N` (`N` the exceptional locus, with null image `φ '' N`),
`∫⁻ x in φ '' V, g x = ∫⁻ x in V \ N, ofReal |det (φ' x)| · g (φ x)`. The single-step c-o-v
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul` on `V \ N`) plus the null-drop `φ '' V =ᵐ
φ '' (V \ N)` (their symmetric difference lies in the null `φ '' N`). -/
theorem perChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (φ : E → E) (φ' : E → (E →L[ℝ] E)) (V N : Set E)
    (hV : MeasurableSet V) (hN : MeasurableSet N)
    (hφ' : ∀ x ∈ V \ N, HasFDerivWithinAt φ (φ' x) (V \ N) x)
    (hinj : InjOn φ (V \ N)) (hNnull : μ (φ '' N) = 0) (g : E → ℝ≥0∞) :
    ∫⁻ x in φ '' V, g x ∂μ = ∫⁻ x in V \ N, ENNReal.ofReal |(φ' x).det| * g (φ x) ∂μ := by
  rw [← lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hV.diff hN) hφ' hinj g]
  apply setLIntegral_congr
  rw [ae_eq_set]
  refine ⟨measure_mono_null ?_ hNnull, ?_⟩
  · rintro y ⟨⟨x, hxV, rfl⟩, hy⟩
    by_cases hxN : x ∈ N
    · exact ⟨x, hxN, rfl⟩
    · exact absurd ⟨x, ⟨hxV, hxN⟩, rfl⟩ hy
  · have : φ '' (V \ N) \ φ '' V = ∅ := by rw [diff_eq_empty]; exact image_mono diff_subset
    rw [this]; exact measure_empty

/-- **G5-abstract, flat-cover form.** A threshold integral over `U` glues to the sum of per-chart
integrals over a finite chart cover: if `U =ᵐ ⋃_{i∈s} φ_i '' V_i` (the leaf images cover `U` up to
null, a.e.-disjoint), each chart C¹ + `InjOn` off a null-image exceptional `N_i`, then
`∫⁻ x in U, g x = Σ_{i∈s} ∫⁻ x in V_i \ N_i, ofReal |det (φ_i' x)| · g (φ_i x)`.
Cover-additivity (`lintegral_biUnion_finset₀`) over the leaves + `perChart` per leaf. The
`(2,2,2)` cover is the instance `g = |F|^{−c}`, `s` the 24 leaves. -/
theorem g5_flat_cover {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} (s : Finset ι) (φ : ι → E → E) (φ' : ι → E → (E →L[ℝ] E)) (V N : ι → Set E)
    (U : Set E)
    (hV : ∀ i ∈ s, MeasurableSet (V i)) (hN : ∀ i ∈ s, MeasurableSet (N i))
    (hφ' : ∀ i ∈ s, ∀ x ∈ V i \ N i, HasFDerivWithinAt (φ i) (φ' i x) (V i \ N i) x)
    (hinj : ∀ i ∈ s, InjOn (φ i) (V i \ N i)) (hNnull : ∀ i ∈ s, μ ((φ i) '' (N i)) = 0)
    (hcover : U =ᵐ[μ] ⋃ i ∈ s, (φ i) '' (V i))
    (hdisj : Set.Pairwise (↑s) (Function.onFun (AEDisjoint μ) (fun i : ι => (φ i) '' (V i))))
    (hmeas : ∀ i ∈ s, NullMeasurableSet ((φ i) '' (V i)) μ)
    (g : E → ℝ≥0∞) :
    ∫⁻ x in U, g x ∂μ
      = ∑ i ∈ s, ∫⁻ x in V i \ N i, ENNReal.ofReal |(φ' i x).det| * g (φ i x) ∂μ := by
  have hbi : ∫⁻ x in (⋃ i ∈ s, (φ i) '' (V i)), g x ∂μ
      = ∑ i ∈ s, ∫⁻ x in (φ i) '' (V i), g x ∂μ :=
    lintegral_biUnion_finset₀ hdisj hmeas g
  rw [setLIntegral_congr hcover, hbi]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact perChart μ (φ i) (φ' i) (V i) (N i) (hV i hi) (hN i hi) (hφ' i hi) (hinj i hi)
    (hNnull i hi) g

/-- **G5-step** (pp's `g5-abstract-statement.md` card form, the `(2,2,2)` consumer). The cover is by
the **injective-locus images** `φ_i '' (V_i \ Z_i)` directly (the caller drops the exceptional `Z_i`
at the cover level), so each term is the c-o-v on `V_i \ Z_i` with no per-term null-drop:
`∫⁻ x in U, g = Σ_{i∈s} ∫⁻ x in V_i \ Z_i, ofReal |det (φ_i' x)| · g (φ_i x)`. This is what the
`(2,2,2)` cover discharges (`H-null/inj/cover/disj` from the explicit charts); the 24-leaf
`∫⁻=Σ∫⁻` is `g5_step` composed 3-deep (step-1 4-way ∘ step-2 3-way ∘ step-3 4-way). -/
theorem g5_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} (s : Finset ι) (φ : ι → E → E) (φ' : ι → E → (E →L[ℝ] E)) (V Z : ι → Set E)
    (U : Set E)
    (hVZ : ∀ i ∈ s, MeasurableSet (V i \ Z i))
    (hφ' : ∀ i ∈ s, ∀ x ∈ V i \ Z i, HasFDerivWithinAt (φ i) (φ' i x) (V i \ Z i) x)
    (hinj : ∀ i ∈ s, InjOn (φ i) (V i \ Z i))
    (hcover : U =ᵐ[μ] ⋃ i ∈ s, (φ i) '' (V i \ Z i))
    (hdisj : Set.Pairwise (↑s) (Function.onFun (AEDisjoint μ) (fun i : ι => (φ i) '' (V i \ Z i))))
    (hmeas : ∀ i ∈ s, NullMeasurableSet ((φ i) '' (V i \ Z i)) μ)
    (g : E → ℝ≥0∞) :
    ∫⁻ x in U, g x ∂μ
      = ∑ i ∈ s, ∫⁻ x in V i \ Z i, ENNReal.ofReal |(φ' i x).det| * g (φ i x) ∂μ := by
  rw [setLIntegral_congr hcover, lintegral_biUnion_finset₀ hdisj hmeas g]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hVZ i hi) (hφ' i hi) (hinj i hi) g

end DLNFibre.DLN.RLCT
