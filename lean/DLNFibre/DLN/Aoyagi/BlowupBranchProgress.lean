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

/-- A branch state carrying both the finite branch position `(S,J)` and the
recurrence-level data over the labels introduced at that position.

This is a bookkeeping state for progress only.  It does not assert that the
recurrence data came from a produced chart or a transition invariant. -/
structure AoyagiRecurrenceBranchState (L : ℕ) (n : ℕ → ℕ) (α : Type*) where
  S : ℕ
  J : ℕ
  stage_pos : 1 ≤ S
  stage_le : S ≤ L
  recurrence : IntroducedLabelRecurrenceState L n S J α

namespace AoyagiRecurrenceBranchState

/-- The finite support of labels introduced at a recurrence-aware branch
state. -/
def support {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : Finset (Σ _ : ℕ, ℕ) :=
  introducedLabelFinset L n s.S s.J

/-- Forget the recurrence data, retaining only the support-growth branch
state. -/
def toIntroducedState {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) :
    AoyagiIntroducedLabelBranchState L n where
  S := s.S
  J := s.J
  stage_pos := s.stage_pos
  stage_le := s.stage_le

/-- The number of actual-width source labels not yet introduced. -/
def remaining (L : ℕ) (n : ℕ → ℕ) {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : ℕ :=
  (actualWidthLabelFinset L n).card - s.support.card

/-- The recurrence-aware remaining-label coordinate agrees with the
support-only branch state's remaining-label coordinate. -/
theorem remaining_eq_toIntroducedState_remaining
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) :
    remaining L n s =
      AoyagiIntroducedLabelBranchState.remaining L n s.toIntroducedState := by
  rfl

/-- The number of already introduced labels whose recurrence level is still
above the current pivot level. -/
def abovePivotCount {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : ℕ :=
  s.recurrence.abovePivotLevelFinset.card

/-- The remaining stage budget.  This coordinate handles stage handoffs where
the introduced-label support may stay unchanged. -/
def stageBudget {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : ℕ :=
  L + 1 - s.S

/-- The fixed base used to encode the stage coordinate. -/
def progressStageBase (L : ℕ) : ℕ :=
  L + 2

/-- The fixed base used to append the above-pivot coordinate to the weighted
remaining/stage block.  The above-pivot coordinate is always strictly smaller
than this base. -/
def progressWeightBase (L : ℕ) (n : ℕ → ℕ) : ℕ :=
  (actualWidthLabelFinset L n).card + 1

/-- Weighted progress measure: first decrease the number of not-yet introduced
labels; when that is unchanged, decrease the stage budget; when both are
unchanged, decrease the above-pivot old-label count. -/
def progressMeasure (L : ℕ) (n : ℕ → ℕ) {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : ℕ :=
  (remaining L n s * progressStageBase L + s.stageBudget) *
    progressWeightBase L n + s.abovePivotCount

/-- The recurrence-aware support is always contained in the finite actual-width
source-label set. -/
theorem support_subset_actual {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) :
    s.support ⊆ actualWidthLabelFinset L n := by
  intro p hp
  exact mem_actualWidthLabelFinset.mpr
    (actualWidthLabel_of_introducedLabel (mem_introducedLabelFinset.mp hp))

/-- The above-pivot count is bounded by the number of actual-width source
labels. -/
theorem abovePivotCount_le_actualWidthCard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) :
    s.abovePivotCount ≤ (actualWidthLabelFinset L n).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  have hp' := (IntroducedLabelRecurrenceState.mem_abovePivotLevelFinset
    s.recurrence p).mp hp
  exact mem_actualWidthLabelFinset.mpr
    (actualWidthLabel_of_introducedLabel hp'.1)

/-- The above-pivot count is strictly below the progress-measure base. -/
theorem abovePivotCount_lt_progressWeightBase
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) :
    s.abovePivotCount < progressWeightBase L n := by
  have hle := abovePivotCount_le_actualWidthCard s
  dsimp [progressWeightBase]
  omega

/-- The stage budget is strictly below its encoding base. -/
theorem stageBudget_lt_progressStageBase
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) :
    s.stageBudget < progressStageBase L := by
  dsimp [stageBudget, progressStageBase]
  omega

/-- Strict support growth decreases the first coordinate of the combined
measure. -/
theorem remaining_lt_of_support_ssubset
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {child parent : AoyagiRecurrenceBranchState L n α}
    (h : parent.support ⊂ child.support) :
    remaining L n child < remaining L n parent := by
  have hcard : parent.support.card < child.support.card := Finset.card_lt_card h
  have hchild :
      child.support.card ≤ (actualWidthLabelFinset L n).card :=
    Finset.card_le_card (support_subset_actual child)
  simp [remaining]
  omega

/-- Support monotonicity weakly decreases the remaining-label coordinate. -/
theorem remaining_le_of_support_subset
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {child parent : AoyagiRecurrenceBranchState L n α}
    (h : parent.support ⊆ child.support) :
    remaining L n child ≤ remaining L n parent := by
  have hcard : parent.support.card ≤ child.support.card := Finset.card_le_card h
  have hchild :
      child.support.card ≤ (actualWidthLabelFinset L n).card :=
    Finset.card_le_card (support_subset_actual child)
  simp [remaining]
  omega

/-- A bounded second coordinate lets a strict first-coordinate decrease
decrease the usual weighted natural encoding. -/
theorem weightedNat_lt_of_left_lt {a a' b b' base : ℕ}
    (hb : b < base) (ha : a < a') :
    a * base + b < a' * base + b' := by
  have hsucc_le : a + 1 ≤ a' := Nat.succ_le_of_lt ha
  have hlt_succ : a * base + b < (a + 1) * base := by
    rw [Nat.add_one_mul]
    exact Nat.add_lt_add_left hb (a * base)
  have hle_parent : (a + 1) * base ≤ a' * base :=
    Nat.mul_le_mul_right base hsucc_le
  have hle_parent_add : a' * base ≤ a' * base + b' :=
    Nat.le_add_right _ _
  exact lt_of_lt_of_le hlt_succ (le_trans hle_parent hle_parent_add)

/-- A decrease in the first coordinate decreases the weighted natural measure,
regardless of the lower coordinates. -/
theorem progressMeasure_lt_of_remaining_lt
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {child parent : AoyagiRecurrenceBranchState L n α}
    (hremaining : remaining L n child < remaining L n parent) :
    progressMeasure L n child < progressMeasure L n parent := by
  let stageBase := progressStageBase L
  let aboveBase := progressWeightBase L n
  let childBlock := remaining L n child * stageBase + child.stageBudget
  let parentBlock := remaining L n parent * stageBase + parent.stageBudget
  have hchildStage : child.stageBudget < stageBase := by
    simpa [stageBase] using stageBudget_lt_progressStageBase child
  have hblock : childBlock < parentBlock := by
    simpa [childBlock, parentBlock, stageBase] using
      weightedNat_lt_of_left_lt
        (b' := parent.stageBudget) hchildStage hremaining
  have hchildAbove : child.abovePivotCount < aboveBase := by
    simpa [aboveBase] using abovePivotCount_lt_progressWeightBase child
  simpa [progressMeasure, childBlock, parentBlock, stageBase, aboveBase] using
    weightedNat_lt_of_left_lt
      (b' := parent.abovePivotCount) hchildAbove hblock

/-- If the introduced-label coordinate is unchanged, a decrease in the stage
budget decreases the weighted natural measure. -/
theorem progressMeasure_lt_of_remaining_eq_of_stageBudget_lt
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {child parent : AoyagiRecurrenceBranchState L n α}
    (hremaining : remaining L n child = remaining L n parent)
    (hstage : child.stageBudget < parent.stageBudget) :
    progressMeasure L n child < progressMeasure L n parent := by
  let aboveBase := progressWeightBase L n
  let childBlock :=
    remaining L n child * progressStageBase L + child.stageBudget
  let parentBlock :=
    remaining L n parent * progressStageBase L + parent.stageBudget
  have hblock : childBlock < parentBlock := by
    simpa [childBlock, parentBlock, hremaining] using
      Nat.add_lt_add_left hstage
        (remaining L n parent * progressStageBase L)
  have hchildAbove : child.abovePivotCount < aboveBase := by
    simpa [aboveBase] using abovePivotCount_lt_progressWeightBase child
  simpa [progressMeasure, childBlock, parentBlock, aboveBase] using
    weightedNat_lt_of_left_lt
      (b' := parent.abovePivotCount) hchildAbove hblock

/-- If the introduced-label and stage coordinates are unchanged, a decrease in
the above-pivot count decreases the weighted natural measure. -/
theorem progressMeasure_lt_of_remaining_eq_of_stageBudget_eq_of_abovePivotCount_lt
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {child parent : AoyagiRecurrenceBranchState L n α}
    (hremaining : remaining L n child = remaining L n parent)
    (hstage : child.stageBudget = parent.stageBudget)
    (habove : child.abovePivotCount < parent.abovePivotCount) :
    progressMeasure L n child < progressMeasure L n parent := by
  simpa [progressMeasure, hremaining, hstage] using
    Nat.add_lt_add_left habove
      ((remaining L n parent * progressStageBase L + parent.stageBudget) *
        progressWeightBase L n)

/-- Combined recurrence-aware progress relation. -/
def progressStep (L : ℕ) (n : ℕ → ℕ) (α : Type*) :
    AoyagiRecurrenceBranchState L n α →
      AoyagiRecurrenceBranchState L n α → Prop :=
  fun child parent ↦ progressMeasure L n child < progressMeasure L n parent

/-- The combined recurrence-aware progress relation is well-founded. -/
theorem progressStep_wellFounded
    (L : ℕ) (n : ℕ → ℕ) (α : Type*) :
    WellFounded (progressStep L n α) :=
  InvImage.wf (progressMeasure L n) Nat.lt_wfRel.wf

/-- A first-coordinate decrease gives a combined progress step. -/
theorem progressStep_of_remaining_lt
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {child parent : AoyagiRecurrenceBranchState L n α}
    (hremaining : remaining L n child < remaining L n parent) :
    progressStep L n α child parent :=
  progressMeasure_lt_of_remaining_lt hremaining

/-- Support-only introduced-label progress gives recurrence-aware progress by
decreasing the first coordinate of the combined measure. -/
theorem progressStep_of_toIntroducedState_progress
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {child parent : AoyagiRecurrenceBranchState L n α}
    (h :
      AoyagiIntroducedLabelBranchState.progressStep L n
        child.toIntroducedState parent.toIntroducedState) :
    progressStep L n α child parent := by
  exact progressStep_of_remaining_lt h

/-- A weak first-coordinate decrease and strict stage-budget decrease give a
combined progress step. -/
theorem progressStep_of_remaining_le_of_stageBudget_lt
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {child parent : AoyagiRecurrenceBranchState L n α}
    (hremaining : remaining L n child ≤ remaining L n parent)
    (hstage : child.stageBudget < parent.stageBudget) :
    progressStep L n α child parent := by
  rcases lt_or_eq_of_le hremaining with hlt | heq
  · exact progressMeasure_lt_of_remaining_lt hlt
  · exact progressMeasure_lt_of_remaining_eq_of_stageBudget_lt heq hstage

/-- A same-support decrease in the above-pivot count gives a combined progress
step. -/
theorem progressStep_of_remaining_eq_of_stageBudget_eq_of_abovePivotCount_lt
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {child parent : AoyagiRecurrenceBranchState L n α}
    (hremaining : remaining L n child = remaining L n parent)
    (hstage : child.stageBudget = parent.stageBudget)
    (habove : child.abovePivotCount < parent.abovePivotCount) :
    progressStep L n α child parent :=
  progressMeasure_lt_of_remaining_eq_of_stageBudget_eq_of_abovePivotCount_lt
    hremaining hstage habove

/-- Replace only the recurrence data, staying over the same branch domain
`(S,J)`. -/
def sameDomainWithRecurrence
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    (recurrence : IntroducedLabelRecurrenceState L n s.S s.J α) :
    AoyagiRecurrenceBranchState L n α where
  S := s.S
  J := s.J
  stage_pos := s.stage_pos
  stage_le := s.stage_le
  recurrence := recurrence

/-- Advance to `(S,J+1)` with supplied recurrence data over the larger
introduced-label domain. -/
def sameStageChildWithRecurrence
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    (recurrence : IntroducedLabelRecurrenceState L n s.S (s.J + 1) α) :
    AoyagiRecurrenceBranchState L n α where
  S := s.S
  J := s.J + 1
  stage_pos := s.stage_pos
  stage_le := s.stage_le
  recurrence := recurrence

/-- Advance to the next stage with `J=0` and supplied recurrence data over the
new stage domain. -/
def stageSuccZeroWithRecurrence
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    (hstage : s.S + 1 ≤ L)
    (recurrence : IntroducedLabelRecurrenceState L n (s.S + 1) 0 α) :
    AoyagiRecurrenceBranchState L n α where
  S := s.S + 1
  J := 0
  stage_pos := by omega
  stage_le := hstage
  recurrence := recurrence

/-- Case 2 recurrence successor as a recurrence-aware branch child. -/
def case2SuccChild
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) (u : α) :
    AoyagiRecurrenceBranchState L n α :=
  sameStageChildWithRecurrence s (s.recurrence.case2Succ u)

/-- Case 1(1) selected-old level move as a same-domain recurrence-aware branch
child. -/
def case1SelectedOldLevelMove
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) (s0 k0 : ℕ) :
    AoyagiRecurrenceBranchState L n α :=
  sameDomainWithRecurrence s (s.recurrence.case1SelectedOldLevelMove s0 k0)

/-- Same-stage support growth gives combined recurrence-aware progress.  The
recurrence data of the child is arbitrary here; this theorem uses only the
finite introduced-label domain growth. -/
theorem sameStageChildWithRecurrence_progress_of_actualWidth
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    (recurrence : IntroducedLabelRecurrenceState L n s.S (s.J + 1) α)
    (hJ : s.J + 1 ≤ n (s.S + 1)) :
    progressStep L n α (sameStageChildWithRecurrence s recurrence) s := by
  exact progressStep_of_remaining_lt
    (remaining_lt_of_support_ssubset (by
      simpa [support, sameStageChildWithRecurrence] using
        AoyagiIntroducedLabelBranchState.support_ssubset_case2_increment
          L n s.stage_pos s.stage_le hJ))

/-- The prefix-minimum continuation bound gives same-stage combined progress. -/
theorem sameStageChildWithRecurrence_progress_of_prefixBound
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    (recurrence : IntroducedLabelRecurrenceState L n s.S (s.J + 1) α)
    (hJ : s.J + 1 ≤ prefixMinNat n (s.S + 1)) :
    progressStep L n α (sameStageChildWithRecurrence s recurrence) s :=
  sameStageChildWithRecurrence_progress_of_actualWidth s recurrence
    (le_trans hJ (prefixMinNat_le_width n (by omega : 1 ≤ s.S + 1)))

/-- The concrete Case 2 recurrence successor gives combined progress under the
prefix-minimum continuation bound. -/
theorem case2SuccChild_progress_of_prefixBound
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) (u : α)
    (hJ : s.J + 1 ≤ prefixMinNat n (s.S + 1)) :
    progressStep L n α (s.case2SuccChild u) s :=
  sameStageChildWithRecurrence_progress_of_prefixBound s
    (s.recurrence.case2Succ u) hJ

/-- A displayed Case 1(2) row-strip `J`-increment payload gives combined
progress for any supplied recurrence data over the pre- and post-domains. -/
theorem sameStageChildWithRecurrence_progress_of_case1DisplayedRowStripPayload
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (payload :
      Case1DisplayedRowStripJIncrementPayload L n S J t numerator leastValue)
    (preRecurrence : IntroducedLabelRecurrenceState L n S J α)
    (postRecurrence : IntroducedLabelRecurrenceState L n S (J + 1) α) :
    progressStep L n α
      ⟨S, J + 1, payload.newLabelActualWidth.1,
        payload.newLabelActualWidth.2.1, postRecurrence⟩
      ⟨S, J, payload.newLabelActualWidth.1,
        payload.newLabelActualWidth.2.1, preRecurrence⟩ := by
  let parent : AoyagiRecurrenceBranchState L n α :=
    ⟨S, J, payload.newLabelActualWidth.1,
      payload.newLabelActualWidth.2.1, preRecurrence⟩
  change progressStep L n α
    (sameStageChildWithRecurrence parent postRecurrence) parent
  exact sameStageChildWithRecurrence_progress_of_actualWidth parent postRecurrence
    payload.newLabelActualWidth.2.2.2

/-- A displayed Case 2 `J`-increment payload gives combined progress for any
supplied recurrence data over the pre- and post-domains. -/
theorem sameStageChildWithRecurrence_progress_of_case2DisplayedPayload
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (payload : Case2DisplayedJIncrementPayload L n S J t numerator leastValue)
    (preRecurrence : IntroducedLabelRecurrenceState L n S J α)
    (postRecurrence : IntroducedLabelRecurrenceState L n S (J + 1) α) :
    progressStep L n α
      ⟨S, J + 1, payload.newLabelActualWidth.1,
        payload.newLabelActualWidth.2.1, postRecurrence⟩
      ⟨S, J, payload.newLabelActualWidth.1,
        payload.newLabelActualWidth.2.1, preRecurrence⟩ := by
  let parent : AoyagiRecurrenceBranchState L n α :=
    ⟨S, J, payload.newLabelActualWidth.1,
      payload.newLabelActualWidth.2.1, preRecurrence⟩
  change progressStep L n α
    (sameStageChildWithRecurrence parent postRecurrence) parent
  exact sameStageChildWithRecurrence_progress_of_actualWidth parent postRecurrence
    payload.newLabelActualWidth.2.2.2

/-- A stage handoff `(S,J) -> (S+1,0)` gives combined progress from finite
domain monotonicity and strict stage-budget decrease.  The recurrence data of
the child is supplied; no source-production claim is made. -/
theorem stageSuccZeroWithRecurrence_progress
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    (hstage : s.S + 1 ≤ L)
    (recurrence : IntroducedLabelRecurrenceState L n (s.S + 1) 0 α) :
    progressStep L n α
      (stageSuccZeroWithRecurrence s hstage recurrence) s := by
  exact progressStep_of_remaining_le_of_stageBudget_lt
    (remaining_le_of_support_subset (by
      simpa [support, stageSuccZeroWithRecurrence] using
        introducedLabelFinset_subset_of_state_le
          (L := L) (n := n) (S := s.S) (J := s.J)
          (S' := s.S + 1) (J' := 0)
          (Or.inl (Nat.lt_succ_self s.S))))
    (by
      dsimp [stageBudget, stageSuccZeroWithRecurrence]
      omega)

/-- Replacing the recurrence data over the same domain by an above-pivot
progress step gives combined recurrence-aware progress. -/
theorem sameDomainWithRecurrence_progress_of_abovePivotProgress
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    {recurrence : IntroducedLabelRecurrenceState L n s.S s.J α}
    (h :
      IntroducedLabelRecurrenceState.abovePivotLevelProgress
        (L := L) (n := n) (S := s.S) (J := s.J) (α := α)
        recurrence s.recurrence) :
    progressStep L n α (sameDomainWithRecurrence s recurrence) s := by
  exact progressStep_of_remaining_eq_of_stageBudget_eq_of_abovePivotCount_lt
    (by simp [remaining, support, sameDomainWithRecurrence])
    (by simp [stageBudget, sameDomainWithRecurrence])
    (by simpa [abovePivotCount, sameDomainWithRecurrence] using h)

/-- Supplied Case 1(1) selected-old level-move data gives combined
same-domain recurrence-aware progress. -/
theorem sameDomainWithRecurrence_progress_of_case1SelectedOldLevelMoveData
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    {J1 s0 k0 : ℕ}
    {postRecurrence : IntroducedLabelRecurrenceState L n s.S s.J α}
    {u : α}
    (data :
      IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData
        (J1 := J1) s.recurrence postRecurrence s0 k0 u)
    (hJ1 : 1 ≤ J1) :
    progressStep L n α (sameDomainWithRecurrence s postRecurrence) s :=
  sameDomainWithRecurrence_progress_of_abovePivotProgress s
    (IntroducedLabelRecurrenceState.abovePivotLevelProgress_of_case1SelectedOldLevelMoveData
      data hJ1)

/-- The concrete Case 1(1) selected-old level move gives combined same-domain
recurrence-aware progress. -/
theorem case1SelectedOldLevelMove_progress_of_sameDomain
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    {J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (sameDomain :
      Case1SelectedOldSuppliedSameDomainBoundary L n s.S s.J J1 s0 k0
        s.recurrence.level t t' numerator numerator' leastValue leastValue') :
    progressStep L n α (s.case1SelectedOldLevelMove s0 k0) s :=
  sameDomainWithRecurrence_progress_of_abovePivotProgress s
    (IntroducedLabelRecurrenceState.abovePivotLevelProgress_case1SelectedOldLevelMove_of_sameDomain
      s.recurrence sameDomain)

end AoyagiRecurrenceBranchState

end Aoyagi
end DLN
end DLNFibre
