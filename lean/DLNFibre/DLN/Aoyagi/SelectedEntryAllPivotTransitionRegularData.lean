import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotRegularData

/-!
# All-pivot selected-entry transition regularity data

This file packages the finite selected-entry chart transition formula as
`SelectedEntryAnalyticTransitionRegularData` for the shared all-pivot
selected-entry atlas context.  The transition domain from a source pivot to a
target pivot is the normalized-target-coordinate nonzero overlap.

It does not prove source production, branch termination, source-prior
transport, determinant-chart Haar transport, a full analytic atlas producer,
normal-crossing extraction, pole order, or an RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace SelectedEntrySignedBox
namespace CenterCoord

variable {ι : Type*} [DecidableEq ι]

private theorem continuousOn_prod_mk
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {s : Set α} {f : α → β} {g : α → γ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x, g x)) s := by
  intro x hx
  rw [continuousWithinAt_prod_iff]
  exact ⟨hf x hx, hg x hx⟩

/-- Denominator for changing from an all-pivot selected-entry source chart to
a target chart. -/
def allPivotTransitionDenom
    {center : Finset ι} (chartEquiv : Fin center.card ≃ center)
    (source target : Fin center.card)
    (x : FormalChartPoint (chartEquiv source)) : ℝ :=
  selectedEntryNormalizedMap (chartEquiv source).1
    (chartPointResidual (chartEquiv source) x) (chartEquiv target).1

/-- The normalized-target-coordinate overlap from source chart to target chart. -/
def allPivotTransitionDomain
    {center : Finset ι} (chartEquiv : Fin center.card ≃ center)
    (source target : Fin center.card) :
    Set (FormalChartPoint (chartEquiv source)) :=
  {x | allPivotTransitionDenom chartEquiv source target x ≠ 0}

/-- Target chart point for the all-pivot selected-entry transition formula. -/
def allPivotTransitionPoint
    {center : Finset ι} (chartEquiv : Fin center.card ≃ center)
    (source target : Fin center.card)
    (x : FormalChartPoint (chartEquiv source)) :
    FormalChartPoint (chartEquiv target) :=
  let denom := allPivotTransitionDenom chartEquiv source target x
  (x.1 * denom,
    fun p : (center.erase (chartEquiv target).1 : Finset ι) =>
      selectedEntryNormalizedMap (chartEquiv source).1
        (chartPointResidual (chartEquiv source) x) p.1 / denom)

/-- The all-pivot transition point is the existing finite transition formula
applied to the visible chart-point residual extension. -/
theorem allPivotTransitionPoint_eq_sourceChartTransitionPoint
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (source target : Fin center.card)
    (x : FormalChartPoint (chartEquiv source)) :
    allPivotTransitionPoint chartEquiv source target x =
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint
        (K := ℝ) hcenter chartEquiv source target x.1
        (chartPointResidual (chartEquiv source) x) :=
  rfl

/-- Rebuilding an all-pivot source chart point from its visible residual
extension recovers the original chart point. -/
theorem sourceChartPoint_chartPointResidual_eq_allPivot
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (source : Fin center.card)
    (x : FormalChartPoint (chartEquiv source)) :
    selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint
        (K := ℝ) hcenter chartEquiv source x.1
        (chartPointResidual (chartEquiv source) x) =
      x := by
  simpa [selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint]
    using sourceChartPoint_chartPointResidual_eq (chartEquiv source) x

/-- The transition denominator is continuous in the source chart point. -/
theorem continuous_allPivotTransitionDenom
    {center : Finset ι} (chartEquiv : Fin center.card ≃ center)
    (source target : Fin center.card) :
    Continuous (fun x : FormalChartPoint (chartEquiv source) =>
      allPivotTransitionDenom chartEquiv source target x) := by
  by_cases htarget :
      (chartEquiv target).1 = (chartEquiv source).1
  · have hfun :
        (fun x : FormalChartPoint (chartEquiv source) =>
          allPivotTransitionDenom chartEquiv source target x) =
        fun _ => (1 : ℝ) := by
      funext x
      simp [allPivotTransitionDenom, selectedEntryNormalizedMap, htarget]
    rw [hfun]
    exact continuous_const
  · have hmem :
        (chartEquiv target).1 ∈ center.erase (chartEquiv source).1 := by
      simp [Finset.mem_erase, htarget, (chartEquiv target).2]
    have hfun :
        (fun x : FormalChartPoint (chartEquiv source) =>
          allPivotTransitionDenom chartEquiv source target x) =
        fun x => x.2 ⟨(chartEquiv target).1, hmem⟩ := by
      funext x
      simp [allPivotTransitionDenom, chartPointResidual,
        selectedEntryNormalizedMap, htarget, hmem]
    rw [hfun]
    exact (continuous_apply (⟨(chartEquiv target).1, hmem⟩ :
      (center.erase (chartEquiv source).1 : Finset ι))).comp continuous_snd

/-- Each normalized coordinate appearing in the transition formula is
continuous in the source chart point. -/
theorem continuous_allPivotTransitionNumerator
    {center : Finset ι} (chartEquiv : Fin center.card ≃ center)
    (source : Fin center.card) (i : center) :
    Continuous (fun x : FormalChartPoint (chartEquiv source) =>
      selectedEntryNormalizedMap (chartEquiv source).1
        (chartPointResidual (chartEquiv source) x) i.1) := by
  by_cases hi : i.1 = (chartEquiv source).1
  · have hfun :
        (fun x : FormalChartPoint (chartEquiv source) =>
          selectedEntryNormalizedMap (chartEquiv source).1
            (chartPointResidual (chartEquiv source) x) i.1) =
        fun _ => (1 : ℝ) := by
      funext x
      simp [selectedEntryNormalizedMap, hi]
    rw [hfun]
    exact continuous_const
  · have hmem : i.1 ∈ center.erase (chartEquiv source).1 := by
      simp [Finset.mem_erase, hi, i.2]
    have hfun :
        (fun x : FormalChartPoint (chartEquiv source) =>
          selectedEntryNormalizedMap (chartEquiv source).1
            (chartPointResidual (chartEquiv source) x) i.1) =
        fun x => x.2 ⟨i.1, hmem⟩ := by
      funext x
      simp [chartPointResidual, selectedEntryNormalizedMap, hi, hmem]
    rw [hfun]
    exact (continuous_apply (⟨i.1, hmem⟩ :
      (center.erase (chartEquiv source).1 : Finset ι))).comp continuous_snd

/-- The all-pivot selected-entry transition formula is continuous on the
normalized-target-coordinate nonzero overlap. -/
theorem continuousOn_allPivotTransitionPoint
    {center : Finset ι} (chartEquiv : Fin center.card ≃ center)
    (source target : Fin center.card) :
    ContinuousOn
      (allPivotTransitionPoint chartEquiv source target)
      (allPivotTransitionDomain chartEquiv source target) := by
  let denomFun : FormalChartPoint (chartEquiv source) → ℝ :=
    fun x => allPivotTransitionDenom chartEquiv source target x
  have hdenom_cont : Continuous denomFun :=
    continuous_allPivotTransitionDenom chartEquiv source target
  have hdenom_on :
      ContinuousOn denomFun
        (allPivotTransitionDomain chartEquiv source target) :=
    hdenom_cont.continuousOn
  have hdenom_ne :
      ∀ x ∈ allPivotTransitionDomain chartEquiv source target,
        denomFun x ≠ 0 := by
    intro x hx
    exact hx
  apply continuousOn_prod_mk
  · have hx1 :
        ContinuousOn (fun x : FormalChartPoint (chartEquiv source) => x.1)
          (allPivotTransitionDomain chartEquiv source target) :=
      continuous_fst.continuousOn
    have hmul := hx1.mul hdenom_on
    simpa [allPivotTransitionPoint, denomFun] using hmul
  · rw [continuousOn_pi]
    intro p
    let i : center := ⟨p.1, (Finset.mem_erase.mp p.2).2⟩
    have hnum_cont :
        Continuous (fun x : FormalChartPoint (chartEquiv source) =>
          selectedEntryNormalizedMap (chartEquiv source).1
            (chartPointResidual (chartEquiv source) x) p.1) := by
      simpa [i] using
        continuous_allPivotTransitionNumerator chartEquiv source i
    have hnum_on :
        ContinuousOn (fun x : FormalChartPoint (chartEquiv source) =>
          selectedEntryNormalizedMap (chartEquiv source).1
            (chartPointResidual (chartEquiv source) x) p.1)
          (allPivotTransitionDomain chartEquiv source target) :=
      hnum_cont.continuousOn
    have hdiv := hnum_on.div hdenom_on hdenom_ne
    simpa [allPivotTransitionPoint, denomFun] using hdiv

set_option linter.style.longLine false in
/-- All-pivot selected-entry transition regularity for the shared
universal-domain all-pivot context. -/
def selectedEntryAllPivotAnalyticTransitionRegularData
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    SelectedEntryAnalyticTransitionRegularData
      (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv) where
  transitionDomain := fun source target =>
    allPivotTransitionDomain chartEquiv source target
  transitionMap := fun source target x =>
    allPivotTransitionPoint chartEquiv source target x
  transitionDomain_subset_chartDomain := by
    intro source target x hx
    trivial
  transition_continuousOn := by
    intro source target
    exact continuousOn_allPivotTransitionPoint chartEquiv source target
  transition_lands := by
    intro source target x hx
    trivial
  transition_preserves_chartMap := by
    intro source target x hx
    have hmap :=
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
        (K := ℝ) hcenter chartEquiv source target x.1
        (chartPointResidual (chartEquiv source) x) hx
    have hsource :
        selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint
            (K := ℝ) hcenter chartEquiv source x.1
            (chartPointResidual (chartEquiv source) x) =
          x :=
      sourceChartPoint_chartPointResidual_eq_allPivot hcenter chartEquiv source x
    simpa [allPivotTransitionPoint_eq_sourceChartTransitionPoint
      hcenter chartEquiv source target x, hsource] using hmap

/-- Forgetful predicate wrapper for all-pivot selected-entry transition
regularity. -/
theorem selectedEntryAllPivotAnalyticTransitionRegular
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    SelectedEntryAnalyticTransitionRegular
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := ℝ) hcenter chartEquiv) := by
  exact ⟨selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv,
    ⟨selectedEntryAllPivotAnalyticTransitionRegularData hcenter chartEquiv⟩⟩

end CenterCoord
end SelectedEntrySignedBox

end Aoyagi
end DLN
end DLNFibre
