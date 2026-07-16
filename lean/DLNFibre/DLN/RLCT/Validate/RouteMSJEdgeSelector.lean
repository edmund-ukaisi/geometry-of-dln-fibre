import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Fin.Tuple.Basic

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeSelector` — the measurable nonzero-index selector (edge brick, Brick-F-adjacent)

Thread `genm-tideD` (edge dispatch arm). A **measurable choice of a nonzero coordinate**: for a measurable
family `v : P → Fin (m+1) → ℝ` that is nonzero a.e., there is a measurable index selector `j₀ : P → Fin (m+1)`
with `v p (j₀ p) ≠ 0` a.e. Consumed by satred's edge-descent lemma (`edgeBackbone`) to fix the pivot column
`j₀(p)` of the fragile direction `v'(p) = Q_inl(p)·ω(p)` for the `|v'_{j₀}|^{−a}` disposal — the
per-`p` `j₀`-choice that has no clean closed form otherwise.

`j₀ p := Fin.find (v p · ≠ 0)` (the LEAST nonzero index, `0` where none); measurable by the fiber
characterization `Fin.find_eq_iff` (`{j₀ = k}` is a finite Boolean combination of the measurable coordinate
loci `{v · j = 0}` / `{v · j ≠ 0}`, via `measurable_to_countable'`), nonzero a.e. by `Fin.find_spec`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal

/-- **Measurable nonzero-index selector.** For a componentwise-measurable `v : P → Fin (m+1) → ℝ` with
`v p ≠ 0` for a.e. `p`, there is a MEASURABLE `j₀ : P → Fin (m+1)` with `v p (j₀ p) ≠ 0` a.e. The selector
is `j₀ p = Fin.find (v p · ≠ 0)` (least nonzero coordinate, `0` where the fragile direction vanishes — a
null set). This supplies the per-`p` pivot column the edge descent's `|v'_{j₀}|^{−a}` disposal needs. -/
theorem exists_measurable_nonzero_index {P : Type*} [MeasurableSpace P] {m : ℕ}
    (v : P → Fin (m + 1) → ℝ) (hv : ∀ j, Measurable (fun p => v p j))
    {μ : Measure P} (hne : ∀ᵐ p ∂μ, v p ≠ 0) :
    ∃ j₀ : P → Fin (m + 1), Measurable j₀ ∧ ∀ᵐ p ∂μ, v p (j₀ p) ≠ 0 := by
  classical
  -- coordinate loci are measurable
  have hzero : ∀ j, MeasurableSet {p | v p j = 0} := fun j => hv j (measurableSet_singleton 0)
  have hne' : ∀ j, MeasurableSet {p | v p j ≠ 0} := fun j =>
    (hv j (measurableSet_singleton 0)).compl
  refine ⟨fun p => if h : ∃ j, v p j ≠ 0 then Fin.find (fun j => v p j ≠ 0) h else 0, ?_, ?_⟩
  · -- measurability via `measurable_to_countable'` (fiber characterization)
    apply measurable_to_countable' (α := Fin (m + 1))
    intro k
    have hset : (fun p => if h : ∃ j, v p j ≠ 0 then Fin.find (fun j => v p j ≠ 0) h else 0) ⁻¹' {k}
        = {p | v p k ≠ 0 ∧ ∀ j, j < k → v p j = 0} ∪ {p | (k = 0) ∧ ∀ j, v p j = 0} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_setOf_eq]
      by_cases hp : ∃ j, v p j ≠ 0
      · simp only [dif_pos hp]
        rw [Fin.find_eq_iff hp]
        constructor
        · rintro ⟨hk, hlt⟩
          exact Or.inl ⟨hk, fun j hj => not_not.mp (hlt j hj)⟩
        · rintro (⟨hk, hlt⟩ | ⟨_, hall⟩)
          · exact ⟨hk, fun j hj hjne => hjne (hlt j hj)⟩
          · exact absurd hp (by simp only [not_exists, ne_eq, not_not]; exact hall)
      · simp only [dif_neg hp]
        simp only [not_exists, ne_eq, not_not] at hp
        constructor
        · intro hk; exact Or.inr ⟨hk.symm, hp⟩
        · rintro (⟨hk, _⟩ | ⟨hk, _⟩)
          · exact absurd (hp k) hk
          · exact hk.symm
    rw [hset]
    refine MeasurableSet.union ?_ ?_
    · refine (hne' k).inter ?_
      change MeasurableSet {p | ∀ j, j < k → v p j = 0}
      rw [Set.setOf_forall]
      refine MeasurableSet.iInter (fun j => ?_)
      by_cases hjk : j < k
      · simpa only [hjk, forall_true_left] using hzero j
      · simp only [hjk, false_implies, Set.setOf_true]; exact MeasurableSet.univ
    · by_cases hk : k = 0
      · have : {p | (k = 0) ∧ ∀ j, v p j = 0} = ⋂ j, {p | v p j = 0} := by
          ext p; simp only [Set.mem_setOf_eq, Set.mem_iInter, hk, true_and]
        rw [this]; exact MeasurableSet.iInter hzero
      · have : {p | (k = 0) ∧ ∀ j, v p j = 0} = ∅ := by
          ext p; simp only [Set.mem_setOf_eq, hk, false_and, Set.mem_empty_iff_false]
        rw [this]; exact MeasurableSet.empty
  · -- nonzero a.e.: on {v p ≠ 0}, `Fin.find` picks a nonzero coordinate
    filter_upwards [hne] with p hp
    have hex : ∃ j, v p j ≠ 0 := Function.ne_iff.mp hp
    simp only [dif_pos hex]
    exact Fin.find_spec (p := fun j => v p j ≠ 0) hex

end DLNFibre.DLN.RLCT
