import DLNFibre.DLN.Aoyagi.BlowupArithmetic

/-!
# Introduced-label progress for Aoyagi blow-up branches

This file proves a small termination kernel for the blow-up bookkeeping:
strict growth of the finite introduced-label support is well-founded, measured
by the number of source labels not yet introduced.

It does not construct source-production payloads, prove that all Case 1/Case 2
branches satisfy the progress relation, or fill the selected-entry analytic
atlas producer's branch-termination field.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- A finite branch state for introduced-label progress bookkeeping. -/
structure AoyagiIntroducedLabelBranchState (L : ℕ) (n : ℕ → ℕ) where
  S : ℕ
  J : ℕ
  stage_pos : 1 ≤ S
  stage_le : S ≤ L

namespace AoyagiIntroducedLabelBranchState

/-- The finite support of labels introduced at this branch state. -/
def support {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n) : Finset (Σ _ : ℕ, ℕ) :=
  introducedLabelFinset L n s.S s.J

/-- The number of finite source labels not yet introduced at this branch state. -/
def remaining (L : ℕ) (n : ℕ → ℕ)
    (s : AoyagiIntroducedLabelBranchState L n) : ℕ :=
  (actualWidthLabelFinset L n).card - s.support.card

/-- The introduced-label support is always a subset of the finite source-label
support. -/
theorem support_subset_actual {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n) :
    s.support ⊆ actualWidthLabelFinset L n := by
  intro p hp
  exact mem_actualWidthLabelFinset.mpr (mem_introducedLabelFinset.mp hp).1

/-- Strict support growth decreases the remaining-label measure. -/
theorem remaining_lt_of_support_ssubset {L : ℕ} {n : ℕ → ℕ}
    {child parent : AoyagiIntroducedLabelBranchState L n}
    (h : parent.support ⊂ child.support) :
    remaining L n child < remaining L n parent := by
  have hcard : parent.support.card < child.support.card := Finset.card_lt_card h
  have hchild :
      child.support.card ≤ (actualWidthLabelFinset L n).card :=
    Finset.card_le_card (support_subset_actual child)
  simp [remaining]
  omega

/-- The progress relation used by the termination kernel: a child state has
strictly fewer remaining finite labels than its parent. -/
def progressStep (L : ℕ) (n : ℕ → ℕ) :
    AoyagiIntroducedLabelBranchState L n →
      AoyagiIntroducedLabelBranchState L n → Prop :=
  fun child parent ↦ remaining L n child < remaining L n parent

/-- Introduced-label progress is well-founded. -/
theorem progressStep_wellFounded (L : ℕ) (n : ℕ → ℕ) :
    WellFounded (progressStep L n) :=
  InvImage.wf (remaining L n) Nat.lt_wfRel.wf

/-- A Case 2 same-stage pivot advance strictly grows introduced-label support. -/
theorem support_ssubset_case2_increment
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L) (hJ : J + 1 ≤ n (S + 1)) :
    (introducedLabelFinset L n S J) ⊂
      introducedLabelFinset L n S (J + 1) := by
  classical
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · exact introducedLabelFinset_subset_of_state_le
      (L := L) (n := n) (S := S) (J := J) (S' := S) (J' := J + 1)
      (Or.inr ⟨rfl, Nat.le_succ J⟩)
  · intro heq
    let p : Σ _ : ℕ, ℕ := ⟨S, J + 1⟩
    have hp_before : p ∉ introducedLabelFinset L n S J := by
      exact fun hp ↦
        not_introducedLabel_case2_new_before L n S J
          (mem_introducedLabelFinset.mp hp)
    have hp_after : p ∈ introducedLabelFinset L n S (J + 1) := by
      exact mem_introducedLabelFinset.mpr
        (introducedLabel_case2_new_after L n hS hSL hJ)
    exact hp_before (by simpa [p, heq] using hp_after)

/-- A Case 2 same-stage pivot advance is a progress step for the finite
introduced-label measure. -/
theorem progressStep_case2_increment
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L) (hJ : J + 1 ≤ n (S + 1)) :
    progressStep L n
      ⟨S, J + 1, hS, hSL⟩
      ⟨S, J, hS, hSL⟩ := by
  exact remaining_lt_of_support_ssubset
    (support_ssubset_case2_increment L n hS hSL hJ)

/-- The Case 2 continuation bound gives the same progress step through the
prefix-minimum bound used in Aoyagi's displayed Case 2 branch. -/
theorem progressStep_case2_increment_of_prefixBound
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hJ : J + 1 ≤ prefixMinNat n (S + 1)) :
    progressStep L n
      ⟨S, J + 1, hS, hSL⟩
      ⟨S, J, hS, hSL⟩ := by
  exact progressStep_case2_increment L n hS hSL
    (le_trans hJ (prefixMinNat_le_width n (by omega : 1 ≤ S + 1)))

/-- The same-stage child state for the displayed Case 2 continuing branch. -/
def case2SameStageChild {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n) :
    AoyagiIntroducedLabelBranchState L n :=
  ⟨s.S, s.J + 1, s.stage_pos, s.stage_le⟩

/-- Displayed Case 2 continuing guard after the pivot at state `(S,J)`. -/
def case2DisplayedContinuingGuard {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n) : Prop :=
  s.J + 2 ≤ prefixMinNat n (s.S + 1)

/-- Displayed Case 2 actual next-width stopped guard after the pivot at
state `(S,J)`. -/
def case2DisplayedActualWidthStoppedGuard {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n) : Prop :=
  n (s.S + 1) = s.J + 1

/-- Displayed Case 2 current-prefix row-exhausted stopped guard after the pivot
at state `(S,J)`. -/
def case2DisplayedRowExhaustedStoppedGuard {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n) : Prop :=
  prefixMinNat n s.S = s.J + 1

/-- Under displayed Case 2 pivot validity, the continuing/actual-width-stopped/
row-exhausted guards cover the finite frontier.  The stopped guards are not
claimed to be exclusive. -/
theorem case2Displayed_frontier_guards_complete {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n)
    (hcont : s.J + 1 ≤ prefixMinNat n (s.S + 1)) :
    case2DisplayedContinuingGuard s ∨
      case2DisplayedActualWidthStoppedGuard s ∨
        case2DisplayedRowExhaustedStoppedGuard s := by
  exact
    case2DisplayedFrontier_next_or_actualWidth_or_rowExhausted_of_cont
      s.stage_pos hcont

/-- Displayed Case 2 pivot validity gives progress from `(S,J)` to the
same-stage child `(S,J+1)`. -/
theorem case2SameStageChild_progress_of_prefixBound {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n)
    (hcont : s.J + 1 ≤ prefixMinNat n (s.S + 1)) :
    progressStep L n (case2SameStageChild s) s := by
  rcases s with ⟨S, J, hS, hSL⟩
  exact progressStep_case2_increment_of_prefixBound L n hS hSL hcont

/-- The displayed Case 2 continuing guard gives progress to the same-stage
child. -/
theorem case2SameStageChild_progress_of_continuingGuard {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n)
    (hnext : case2DisplayedContinuingGuard s) :
    progressStep L n (case2SameStageChild s) s := by
  exact case2SameStageChild_progress_of_prefixBound s (by
    dsimp [case2DisplayedContinuingGuard] at hnext
    omega)

end AoyagiIntroducedLabelBranchState

end Aoyagi
end DLN
end DLNFibre
