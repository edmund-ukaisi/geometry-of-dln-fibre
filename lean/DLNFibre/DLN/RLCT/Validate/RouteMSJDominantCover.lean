import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

-- `Fintype ι` is genuinely used in the proofs (`Finset.univ`, `∑ i`, argmax), not in the result type.
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDominantCover` — the dominant-minor cover-assembly

**Thread `genm-vsdeep` (aoyagi-full), the §8-i det-inverse cover-assembly.** The deeper-strata
finiteness of the `(3,3,3,4)` pivot chart reduces (subred / pivchg §SEAM) to a **dominant-minor cover**:
partition the domain by *which* `q`-minor of the tail carries the rank, so that on each chart the chosen
pivot is dominant and nonzero (`|det B| ≍ σ_q`) and a per-chart majorant is integrable. This module builds
the **cover-assembly** — the pure measure-theoretic skeleton that reduces box-finiteness to per-chart
finiteness — as reusable, network-free bedrock. The analytic per-chart bound (the coupled `σ_q^{−α}`
majorant / the front-first box estimate) is consumed here as a **hypothesis**, not re-derived.

The cover is a **least-index-argmax partition**: index the charts by a finite linearly-ordered `ι`
(the `q`-minor selections), with a real key `key i` (`= |det B_i|`, the minor magnitude). The dominance
cell of `i` is where `key i` is the maximum AND `i` is the least maximiser. This is a **genuine
partition** (not merely a.e.): the least-index tie-break makes the cells pairwise disjoint on the nose, so
`∫box = Σ∫chart` holds **exactly**, with no boundary/seam term (pivchg §SEAM: "the seam contributes
nothing").

* **`dominanceCell key i`** — `{x | (∀ j, key j x ≤ key i x) ∧ (∀ j, j < i → key j x < key i x)}`, the
  least-index-argmax cell (§SEAM checklist items 1+2: dominance-restricted `{|det B_i| ≥ others}`).
* **`iUnion_dominanceCell`** — the cells cover: `⋃ i, dominanceCell key i = univ` (nonempty `ι`).
* **`pairwiseDisjoint_dominanceCell`** — the cells are pairwise disjoint (least-index tie-break).
* **`measurableSet_dominanceCell`** — each cell is measurable (keys measurable).
* **`setLIntegral_eq_sum_dominanceCell`** — the EXACT partition: `∫⁻_D g = ∑ i, ∫⁻_{D ∩ cell i} g`
  (§SEAM: `∫box = Σ∫chart` exactly, no seam term). Stated over an **arbitrary** measure `μ`.
* **`setLIntegral_lt_top_of_dominanceCell`** — the cover-assembly headline: per-chart finiteness ⟹
  box finiteness. The per-chart hypothesis is the bare `∫⁻_{D ∩ cell i} g ∂μ < ⊤` — NO inverse-gap
  factor (§SEAM checklist item 4), under an arbitrary `μ` (so it applies to the pulled-back factor
  measure, §SEAM item 5 / task #116 `D_prod`).
* **`setLIntegral_lt_top_of_detMinorCover`** — the specialization to `key i = |det (minor i)|`, the
  intended dominant-minor form (measurability discharged via `Continuous.matrix_det`).

Network-free (pure measure theory + matrix determinant continuity); `Core`-liftable on a second use.
Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

section Abstract

variable {α : Type*} {ι : Type*} [LinearOrder ι]

/-- **The least-index-argmax dominance cell** of `key i` among the finite family `key`. A point `x` is
in `dominanceCell key i` iff `key i x` is the maximum value `key · x` attains AND `i` is the least index
attaining it. With `key i = |det B_i|` this is the chart `{|det B_i| ≥ |det B_j| ∀ j}` with the
least-index tie-break (pivchg §SEAM checklist items 1+2). -/
def dominanceCell (key : ι → α → ℝ) (i : ι) : Set α :=
  {x | (∀ j, key j x ≤ key i x) ∧ (∀ j, j < i → key j x < key i x)}

/-- Two distinct dominance cells are disjoint (the least-index tie-break). -/
theorem disjoint_dominanceCell (key : ι → α → ℝ) {i j : ι} (hij : i ≠ j) :
    Disjoint (dominanceCell key i) (dominanceCell key j) := by
  rw [Set.disjoint_left]
  rintro x ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact absurd (hi1 j) (not_le.mpr (hj2 i h))
  · exact absurd (hj1 i) (not_le.mpr (hi2 j h))

variable [Fintype ι]

/-- **The dominance cells are pairwise disjoint** — a genuine partition (not merely a.e.). -/
theorem pairwiseDisjoint_dominanceCell (key : ι → α → ℝ) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (dominanceCell key) := by
  intro _ _ _ _ hij; exact disjoint_dominanceCell key hij

/-- **The dominance cells cover the whole space** (`ι` nonempty). At every `x`, the finite family
`key · x` attains a maximum; the least index attaining it selects the cell containing `x`. -/
theorem iUnion_dominanceCell [Nonempty ι] (key : ι → α → ℝ) :
    ⋃ i, dominanceCell key i = Set.univ := by
  classical
  refine Set.eq_univ_of_forall (fun x => Set.mem_iUnion.mpr ?_)
  -- a maximiser `i0`
  obtain ⟨i0, -, hi0⟩ :=
    Finset.exists_max_image Finset.univ (fun i => key i x) Finset.univ_nonempty
  have hmax : ∀ i, key i x ≤ key i0 x := fun i => hi0 i (Finset.mem_univ i)
  -- the maximisers (indices achieving the max value `key i0 x`), and their membership iff
  set S : Finset ι := Finset.univ.filter (fun i => key i x = key i0 x) with hS
  have hSmem : ∀ i, i ∈ S ↔ key i x = key i0 x := by
    intro i; rw [hS, Finset.mem_filter]; simp
  have hSne : S.Nonempty := ⟨i0, (hSmem i0).mpr rfl⟩
  have hmem : key (S.min' hSne) x = key i0 x := (hSmem _).mp (S.min'_mem hSne)
  refine ⟨S.min' hSne, fun j => ?_, fun j hj => ?_⟩
  · -- clause 1: `S.min'` is a maximiser
    rw [hmem]; exact hmax j
  · -- clause 2: no strictly smaller index ties `S.min'`
    have hle : key j x ≤ key (S.min' hSne) x := by rw [hmem]; exact hmax j
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (S.min'_le j ((hSmem j).mpr (by rw [h]; exact hmem))) (not_le.mpr hj)

variable [MeasurableSpace α]

/-- **Each dominance cell is measurable** when the keys are measurable — a finite intersection of the
measurable sublevel/strict-sublevel sets `{key j ≤ key i}` and `{key j < key i}`. -/
theorem measurableSet_dominanceCell {key : ι → α → ℝ} (hkey : ∀ i, Measurable (key i)) (i : ι) :
    MeasurableSet (dominanceCell key i) := by
  have h1 : MeasurableSet {x | ∀ j, key j x ≤ key i x} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_le (hkey j) (hkey i))
  have h2 : MeasurableSet {x | ∀ j, j < i → key j x < key i x} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter (fun j => ?_)
    by_cases hj : j < i
    · have hset : {x | j < i → key j x < key i x} = {x | key j x < key i x} := by
        ext x; simp [hj]
      rw [hset]; exact measurableSet_lt (hkey j) (hkey i)
    · have hset : {x | j < i → key j x < key i x} = Set.univ := by
        ext x; simp [hj]
      rw [hset]; exact MeasurableSet.univ
  exact h1.inter h2

variable {μ : MeasureTheory.Measure α}

/-- **The exact dominant-minor partition** (§SEAM: `∫box = Σ∫chart` EXACTLY, no seam/boundary term).
For any measurable `D`, measurable keys, and nonempty index, the box integral splits as the finite sum
over dominance charts — over an **arbitrary** measure `μ` (so the pulled-back factor measure applies). -/
theorem setLIntegral_eq_sum_dominanceCell [Nonempty ι] {key : ι → α → ℝ}
    (hkey : ∀ i, Measurable (key i)) {D : Set α} (hD : MeasurableSet D) (g : α → ℝ≥0∞) :
    ∫⁻ x in D, g x ∂μ = ∑ i, ∫⁻ x in D ∩ dominanceCell key i, g x ∂μ := by
  have hset : (⋃ i ∈ (Finset.univ : Finset ι), (D ∩ dominanceCell key i)) = D := by
    simp only [Finset.mem_univ, Set.iUnion_true, ← Set.inter_iUnion, iUnion_dominanceCell,
      Set.inter_univ]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι))
      (fun i => D ∩ dominanceCell key i) := by
    intro _ _ _ _ hij
    exact (disjoint_dominanceCell key hij).mono Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ i ∈ (Finset.univ : Finset ι), MeasurableSet (D ∩ dominanceCell key i) :=
    fun i _ => hD.inter (measurableSet_dominanceCell hkey i)
  calc ∫⁻ x in D, g x ∂μ
      = ∫⁻ x in ⋃ i ∈ (Finset.univ : Finset ι), (D ∩ dominanceCell key i), g x ∂μ := by rw [hset]
    _ = ∑ i, ∫⁻ x in D ∩ dominanceCell key i, g x ∂μ :=
        lintegral_biUnion_finset hdisj hmeas g

/-- **The cover-assembly headline** — per-chart finiteness ⟹ box finiteness. Reduces box-finiteness to
the per-chart integrals over the dominance charts. The per-chart hypothesis is the bare
`∫⁻_{D ∩ cell i} g ∂μ < ⊤` — NO inverse-minor-gap factor (§SEAM checklist item 4) — under an arbitrary
`μ` (§SEAM item 5). This is the reduction the front-first box-bound's per-chart `σ_q^{−α}` majorant
feeds. -/
theorem setLIntegral_lt_top_of_dominanceCell [Nonempty ι] {key : ι → α → ℝ}
    (hkey : ∀ i, Measurable (key i)) {D : Set α} (hD : MeasurableSet D) {g : α → ℝ≥0∞}
    (hcharts : ∀ i, ∫⁻ x in D ∩ dominanceCell key i, g x ∂μ < ⊤) :
    ∫⁻ x in D, g x ∂μ < ⊤ := by
  rw [setLIntegral_eq_sum_dominanceCell hkey hD g]
  exact ENNReal.sum_lt_top.mpr (fun i _ => hcharts i)

end Abstract

section DetMinor

open Matrix

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {μ : MeasureTheory.Measure α}

/-- **The dominant-minor cover-assembly, det-minor form** (the intended pivchg §SEAM instance). With the
minor-magnitude key `key i = |det (minor i)|` (continuous ⟹ measurable via `Continuous.matrix_det`),
per-chart finiteness on the dominance charts `{|det (minor i)| ≥ others}` ⟹ box finiteness. This is the
`{|det B|≥others}`-restricted cover pivchg §SEAM item 2 mandates; the per-chart hypothesis carries the
coupled `σ_q^{−α}` majorant (NO inverse-gap factor), under an arbitrary `μ` (the pulled-back factor
measure). -/
theorem setLIntegral_lt_top_of_detMinorCover [Nonempty ι] {q : ℕ}
    (minor : ι → α → Matrix (Fin q) (Fin q) ℝ) (hminor : ∀ i, Continuous (minor i))
    {D : Set α} (hD : MeasurableSet D) {g : α → ℝ≥0∞}
    (hcharts : ∀ i, ∫⁻ x in D ∩ dominanceCell (fun i x => |(minor i x).det|) i, g x ∂μ < ⊤) :
    ∫⁻ x in D, g x ∂μ < ⊤ :=
  setLIntegral_lt_top_of_dominanceCell
    (fun i => ((hminor i).matrix_det.abs).measurable) hD hcharts

end DetMinor

section Nonvacuity

/-- **Non-vacuity** — the cover-assembly headline fires end-to-end on genuine distinct keys. The two
keys `id` and `-·` induce the real dominance partition `{x ≥ 0}` / `{x < 0}`; on any finite measure the
per-chart hypotheses discharge (a finite measure is finite on every measurable set), and the assembly
returns the finite box integral. Demonstrates the hypotheses are jointly satisfiable and the machinery
composes. -/
example (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    {D : Set ℝ} (hD : MeasurableSet D) :
    ∫⁻ _x in D, (1 : ℝ≥0∞) ∂μ < ⊤ := by
  have hk : ∀ i : Fin 2, Measurable (![(id : ℝ → ℝ), Neg.neg] i) := by
    intro i; fin_cases i
    · simpa using (measurable_id : Measurable (id : ℝ → ℝ))
    · simpa using (measurable_neg : Measurable (Neg.neg : ℝ → ℝ))
  refine setLIntegral_lt_top_of_dominanceCell hk hD (fun i => ?_)
  rw [MeasureTheory.setLIntegral_const, one_mul]
  exact measure_lt_top μ _

end Nonvacuity

end DLNFibre.DLN.RLCT
