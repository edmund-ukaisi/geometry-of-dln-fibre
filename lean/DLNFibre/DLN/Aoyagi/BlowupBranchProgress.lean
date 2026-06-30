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

/-- A same-stage advance `(S,J) -> (S,J+1)` strictly grows introduced-label
support whenever the fresh label is actual-width valid. -/
theorem progressStep_sameStage_increment
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L) (hJ : J + 1 ≤ n (S + 1)) :
    progressStep L n
      ⟨S, J + 1, hS, hSL⟩
      ⟨S, J, hS, hSL⟩ :=
  progressStep_case2_increment L n hS hSL hJ

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

/-- A displayed Case 1(2) row-strip `J`-increment payload gives the
same-stage introduced-label progress step `(S,J) -> (S,J+1)`.

This intentionally applies only to the Case 1(2) row-strip continuation
payload.  Case 1(1) is a same-domain selected-old lowering step and is not
visible to the introduced-label support-growth measure. -/
theorem progressStep_case1DisplayedRowStrip_jIncrementPayload
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (payload :
      Case1DisplayedRowStripJIncrementPayload L n S J t numerator leastValue) :
    progressStep L n
      ⟨S, J + 1, payload.newLabelActualWidth.1, payload.newLabelActualWidth.2.1⟩
      ⟨S, J, payload.newLabelActualWidth.1, payload.newLabelActualWidth.2.1⟩ :=
  progressStep_sameStage_increment L n
    payload.newLabelActualWidth.1
    payload.newLabelActualWidth.2.1
    payload.newLabelActualWidth.2.2.2

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

namespace IntroducedLabelRecurrenceState

/-- The finite plateau of introduced old labels whose recurrence level is
`target` at a fixed branch state `(S,J)`. -/
def levelPlateau {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (target : ℕ) :
    Finset (Σ _ : ℕ, ℕ) :=
  (introducedLabelFinset L n S J).filter fun p ↦ state.level p.1 p.2 = target

/-- Membership in a fixed recurrence-level plateau. -/
theorem mem_levelPlateau {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (target : ℕ)
    (p : Σ _ : ℕ, ℕ) :
    p ∈ state.levelPlateau target ↔
      introducedLabel L n S J p.1 p.2 ∧ state.level p.1 p.2 = target := by
  simp [levelPlateau, mem_introducedLabelFinset]

/-- A fixed-level plateau progress relation: the child has fewer introduced
labels at `target` than the parent. -/
def levelPlateauProgress {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (target : ℕ) :
    IntroducedLabelRecurrenceState L n S J α →
      IntroducedLabelRecurrenceState L n S J α → Prop :=
  fun child parent ↦
    (child.levelPlateau target).card < (parent.levelPlateau target).card

/-- Fixed-level plateau progress is well-founded. -/
theorem levelPlateauProgress_wellFounded
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*} (target : ℕ) :
    WellFounded
      (levelPlateauProgress (L := L) (n := n) (S := S) (J := J)
        (α := α) target) :=
  InvImage.wf
    (fun state : IntroducedLabelRecurrenceState L n S J α ↦
      (state.levelPlateau target).card)
    Nat.lt_wfRel.wf

/-- The finite set of introduced old labels whose recurrence level remains
above the current pivot level `J`. -/
def abovePivotLevelFinset {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) :
    Finset (Σ _ : ℕ, ℕ) :=
  (introducedLabelFinset L n S J).filter fun p ↦ J < state.level p.1 p.2

/-- Membership in the above-pivot recurrence-level set. -/
theorem mem_abovePivotLevelFinset {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α)
    (p : Σ _ : ℕ, ℕ) :
    p ∈ state.abovePivotLevelFinset ↔
      introducedLabel L n S J p.1 p.2 ∧ J < state.level p.1 p.2 := by
  simp [abovePivotLevelFinset, mem_introducedLabelFinset]

/-- Same-domain old-label progress: the child has fewer introduced labels
above the pivot level `J` than the parent. -/
def abovePivotLevelProgress {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*} :
    IntroducedLabelRecurrenceState L n S J α →
      IntroducedLabelRecurrenceState L n S J α → Prop :=
  fun child parent ↦
    child.abovePivotLevelFinset.card < parent.abovePivotLevelFinset.card

/-- Same-domain above-pivot level progress is well-founded. -/
theorem abovePivotLevelProgress_wellFounded
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*} :
    WellFounded
      (abovePivotLevelProgress (L := L) (n := n) (S := S) (J := J)
        (α := α)) :=
  InvImage.wf
    (fun state : IntroducedLabelRecurrenceState L n S J α ↦
      state.abovePivotLevelFinset.card)
    Nat.lt_wfRel.wf

/-- A supplied Case 1(1) selected-old level move erases exactly the selected
old label from the plateau at level `J+J1`. -/
theorem levelPlateau_eq_erase_of_case1SelectedOldLevelMoveData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ} {α : Type*}
    {pre post : IntroducedLabelRecurrenceState L n S J α} {u : α}
    (data :
      Case1SelectedOldLevelMoveData (J1 := J1) pre post s0 k0 u)
    (hJ1 : 1 ≤ J1) :
    post.levelPlateau (J + J1) =
      (pre.levelPlateau (J + J1)).erase (Sigma.mk s0 k0) := by
  classical
  ext p
  rcases p with ⟨s, k⟩
  by_cases hp : (s, k) = (s0, k0)
  · have hs : s = s0 := congrArg Prod.fst hp
    have hk : k = k0 := congrArg Prod.snd hp
    subst s
    subst k
    have hJ1_ne : J1 ≠ 0 := by omega
    simp [levelPlateau, mem_introducedLabelFinset, data.selectedIntroduced,
      data.pre_level_selected, data.post_level_selected, hJ1_ne]
  · have hsigma :
        (Sigma.mk s k : Σ _ : ℕ, ℕ) ≠ Sigma.mk s0 k0 := by
      intro h
      cases h
      exact hp rfl
    by_cases hintro : introducedLabel L n S J s k
    · have hlevel := data.level_old hintro hp
      simp [levelPlateau, mem_introducedLabelFinset, hintro, hsigma, hlevel]
    · have hnotmem :
        (Sigma.mk s k : Σ _ : ℕ, ℕ) ∉ introducedLabelFinset L n S J := by
        rw [mem_introducedLabelFinset]
        exact hintro
      simp [levelPlateau, hnotmem, hsigma]

/-- A supplied Case 1(1) selected-old level move strictly decreases the
plateau count at the first-jump level `J+J1`. -/
theorem levelPlateauProgress_of_case1SelectedOldLevelMoveData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ} {α : Type*}
    {pre post : IntroducedLabelRecurrenceState L n S J α} {u : α}
    (data :
      Case1SelectedOldLevelMoveData (J1 := J1) pre post s0 k0 u)
    (hJ1 : 1 ≤ J1) :
    levelPlateauProgress (L := L) (n := n) (S := S) (J := J)
      (α := α) (J + J1) post pre := by
  classical
  change (post.levelPlateau (J + J1)).card < (pre.levelPlateau (J + J1)).card
  rw [levelPlateau_eq_erase_of_case1SelectedOldLevelMoveData data hJ1]
  have hmem : Sigma.mk s0 k0 ∈ pre.levelPlateau (J + J1) := by
    rw [mem_levelPlateau]
    exact ⟨data.selectedIntroduced, data.pre_level_selected⟩
  exact Finset.card_erase_lt_of_mem hmem

/-- The concrete Case 1(1) selected-old level override strictly decreases the
first-jump plateau count. -/
theorem levelPlateauProgress_case1SelectedOldLevelMove_of_sameDomain
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ} {α : Type*}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J α)
    (sameDomain :
      Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 pre.level
        t t' numerator numerator' leastValue leastValue') :
    levelPlateauProgress (L := L) (n := n) (S := S) (J := J)
      (α := α) (J + J1) (pre.case1SelectedOldLevelMove s0 k0) pre :=
  levelPlateauProgress_of_case1SelectedOldLevelMoveData
    (pre.case1SelectedOldLevelMove_levelMoveData sameDomain.selectedIntroduced
      sameDomain.selectedLevel)
    sameDomain.firstJump.positive

/-- A supplied Case 1(1) selected-old level move erases exactly the selected
old label from the finite set of introduced labels above the pivot level. -/
theorem abovePivotLevelFinset_eq_erase_of_case1SelectedOldLevelMoveData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ} {α : Type*}
    {pre post : IntroducedLabelRecurrenceState L n S J α} {u : α}
    (data :
      Case1SelectedOldLevelMoveData (J1 := J1) pre post s0 k0 u)
    (hJ1 : 1 ≤ J1) :
    post.abovePivotLevelFinset =
      pre.abovePivotLevelFinset.erase (Sigma.mk s0 k0) := by
  classical
  ext p
  rcases p with ⟨s, k⟩
  by_cases hp : (s, k) = (s0, k0)
  · have hs : s = s0 := congrArg Prod.fst hp
    have hk : k = k0 := congrArg Prod.snd hp
    subst s
    subst k
    have hpre : J < pre.level s0 k0 := by
      rw [data.pre_level_selected]
      omega
    have hpost : ¬ J < post.level s0 k0 := by
      rw [data.post_level_selected]
      omega
    simp [abovePivotLevelFinset, mem_introducedLabelFinset, data.selectedIntroduced,
      hpre, hpost]
  · have hsigma :
        (Sigma.mk s k : Σ _ : ℕ, ℕ) ≠ Sigma.mk s0 k0 := by
      intro h
      cases h
      exact hp rfl
    by_cases hintro : introducedLabel L n S J s k
    · have hlevel := data.level_old hintro hp
      simp [abovePivotLevelFinset, mem_introducedLabelFinset, hintro, hsigma, hlevel]
    · have hnotmem :
        (Sigma.mk s k : Σ _ : ℕ, ℕ) ∉ introducedLabelFinset L n S J := by
        rw [mem_introducedLabelFinset]
        exact hintro
      simp [abovePivotLevelFinset, hnotmem, hsigma]

/-- A supplied Case 1(1) selected-old level move strictly decreases the
same-domain above-pivot old-label count. -/
theorem abovePivotLevelProgress_of_case1SelectedOldLevelMoveData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ} {α : Type*}
    {pre post : IntroducedLabelRecurrenceState L n S J α} {u : α}
    (data :
      Case1SelectedOldLevelMoveData (J1 := J1) pre post s0 k0 u)
    (hJ1 : 1 ≤ J1) :
    abovePivotLevelProgress (L := L) (n := n) (S := S) (J := J)
      (α := α) post pre := by
  classical
  change post.abovePivotLevelFinset.card < pre.abovePivotLevelFinset.card
  rw [abovePivotLevelFinset_eq_erase_of_case1SelectedOldLevelMoveData data hJ1]
  have hmem : Sigma.mk s0 k0 ∈ pre.abovePivotLevelFinset := by
    rw [mem_abovePivotLevelFinset]
    exact ⟨data.selectedIntroduced, by
      rw [data.pre_level_selected]
      omega⟩
  exact Finset.card_erase_lt_of_mem hmem

/-- The concrete Case 1(1) selected-old level override strictly decreases the
same-domain above-pivot old-label count. -/
theorem abovePivotLevelProgress_case1SelectedOldLevelMove_of_sameDomain
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ} {α : Type*}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J α)
    (sameDomain :
      Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 pre.level
        t t' numerator numerator' leastValue leastValue') :
    abovePivotLevelProgress (L := L) (n := n) (S := S) (J := J)
      (α := α) (pre.case1SelectedOldLevelMove s0 k0) pre :=
  abovePivotLevelProgress_of_case1SelectedOldLevelMoveData
    (pre.case1SelectedOldLevelMove_levelMoveData sameDomain.selectedIntroduced
      sameDomain.selectedLevel)
    sameDomain.firstJump.positive

end IntroducedLabelRecurrenceState

end Aoyagi
end DLN
end DLNFibre
