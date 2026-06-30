import DLNFibre.DLN.Aoyagi.SelectedEntryOneChartJacobianVolumeData

/-!
# One-chart selected-entry regularity data

This file packages chart regularity, identity transition regularity, and unit
regularity for the single selected-entry chart context used by
`SelectedEntryOneChartJacobianVolumeData`.

It does not construct source coverage, source production, branch termination,
a full analytic atlas producer, normal-crossing extraction, pole order, or an
RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace SelectedEntrySignedBox
namespace CenterCoord

variable {ι : Type*} [DecidableEq ι]

/-- The unique selected-entry chart coordinate is the pivot coordinate, hence
is continuous in chart-point coordinates. -/
theorem continuous_chartPointCoord
    {center : Finset ι} (pivot : center) :
    Continuous (fun x : FormalChartPoint pivot =>
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := ℝ) pivot).coord (0 : Fin 1) x (0 : Fin 1)) := by
  change Continuous (fun x : FormalChartPoint pivot => x.1)
  simpa [FormalChartPoint] using
    (continuous_fst :
      Continuous fun x :
        ℝ × ((center.erase pivot.1 : Finset ι) → ℝ) => x.1)

/-- The selected-entry loss unit `1 + sum r_i^2` is continuous in chart-point
coordinates. -/
theorem continuous_chartPointLossUnit
    {center : Finset ι} (pivot : center) :
    Continuous (fun x : FormalChartPoint pivot =>
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := ℝ) pivot).lossUnit (0 : Fin 1) x) := by
  have hunit :
      (fun x : FormalChartPoint pivot =>
        (selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) pivot).lossUnit (0 : Fin 1) x) =
      fun x : FormalChartPoint pivot =>
        selectedEntryCenterSqUnitFactor (center.erase pivot.1)
          (chartPointResidual pivot x) := by
    funext x
    calc
      (selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) pivot).lossUnit (0 : Fin 1) x =
          (selectedEntryCenterSqFormalJacobianChartCertificate
            (K := ℝ) pivot).lossUnit (0 : Fin 1)
            (selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint
              pivot x.1 (chartPointResidual pivot x)) := by
            rw [sourceChartPoint_chartPointResidual_eq pivot x]
      _ = selectedEntryCenterSqUnitFactor (center.erase pivot.1)
          (chartPointResidual pivot x) :=
            selectedEntryCenterSqFormalJacobianChartCertificate.lossUnit_sourceChartPoint_eq
              pivot x.1 (chartPointResidual pivot x)
  rw [hunit]
  change Continuous (fun x : FormalChartPoint pivot =>
    1 + ∑ i ∈ center.erase pivot.1, chartPointResidual pivot x i ^ 2)
  refine continuous_const.add (continuous_finset_sum _ fun i hi => ?_)
  have hterm :
      (fun x : FormalChartPoint pivot => chartPointResidual pivot x i ^ 2) =
        fun x : FormalChartPoint pivot => x.2 ⟨i, hi⟩ ^ 2 := by
    funext x
    simp [chartPointResidual, hi]
  rw [hterm]
  exact (((continuous_apply (⟨i, hi⟩ :
    (center.erase pivot.1 : Finset ι))).comp continuous_snd).pow 2)

/-- The selected-entry Jacobian/prior unit is constantly `1`, hence is
continuous in chart-point coordinates. -/
theorem continuous_chartPointJacobianPriorUnit
    {center : Finset ι} (pivot : center) :
    Continuous (fun x : FormalChartPoint pivot =>
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := ℝ) pivot).jacobianPriorUnit (0 : Fin 1) x) := by
  change Continuous (fun _x : FormalChartPoint pivot => (1 : ℝ))
  exact continuous_const

/-- One-chart chart regularity for the selected-entry context with universal
source and chart domains. -/
def selectedEntryOneChartAnalyticChartRegularData
    {center : Finset ι} (pivot : center) :
    SelectedEntryAnalyticChartRegularData
      (selectedEntryOneChartAnalyticAtlasContext pivot) where
  chartMap_continuousOn := by
    intro _c
    change @ContinuousOn (FormalChartPoint pivot) (center → ℝ)
      inferInstance inferInstance (formalChartMap pivot) Set.univ
    exact (continuous_formalChartMap pivot).continuousOn
  coord_continuousOn := by
    intro _c _j
    change @ContinuousOn (FormalChartPoint pivot) ℝ inferInstance inferInstance
      (fun x : FormalChartPoint pivot =>
        (selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) pivot).coord (0 : Fin 1) x (0 : Fin 1))
      Set.univ
    exact (continuous_chartPointCoord pivot).continuousOn

/-- One-chart identity transition regularity for the selected-entry context.

This is only the single-chart identity transition; it is not a multi-pivot
selected-entry transition theorem. -/
def selectedEntryOneChartAnalyticTransitionRegularData
    {center : Finset ι} (pivot : center) :
    SelectedEntryAnalyticTransitionRegularData
      (selectedEntryOneChartAnalyticAtlasContext pivot) where
  transitionDomain := fun _source _target => Set.univ
  transitionMap := fun _source _target x => x
  transitionDomain_subset_chartDomain := by
    intro _source _target x _hx
    trivial
  transition_continuousOn := by
    intro _source _target
    change @ContinuousOn (FormalChartPoint pivot) (FormalChartPoint pivot)
      inferInstance inferInstance id Set.univ
    exact continuous_id.continuousOn
  transition_lands := by
    intro _source _target x _hx
    trivial
  transition_preserves_chartMap := by
    intro _source _target x _hx
    rfl

/-- One-chart unit regularity for the selected-entry context with universal
chart domain. -/
def selectedEntryOneChartAnalyticUnitRegularData
    {center : Finset ι} (pivot : center) :
    SelectedEntryAnalyticUnitRegularData
      (selectedEntryOneChartAnalyticAtlasContext pivot) where
  lossUnit_continuousOn := by
    intro _c
    change @ContinuousOn (FormalChartPoint pivot) ℝ inferInstance inferInstance
      (fun x : FormalChartPoint pivot =>
        (selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) pivot).lossUnit (0 : Fin 1) x)
      Set.univ
    exact (continuous_chartPointLossUnit pivot).continuousOn
  jacobianPriorUnit_continuousOn := by
    intro _c
    change @ContinuousOn (FormalChartPoint pivot) ℝ inferInstance inferInstance
      (fun x : FormalChartPoint pivot =>
        (selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) pivot).jacobianPriorUnit (0 : Fin 1) x)
      Set.univ
    exact (continuous_chartPointJacobianPriorUnit pivot).continuousOn
  lossUnit_isUnit_on := by
    intro c x _hx
    exact
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := ℝ) pivot).lossUnit_isUnit c x
  jacobianPriorUnit_isUnit_on := by
    intro c x _hx
    exact
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := ℝ) pivot).jacobianPriorUnit_isUnit c x

end CenterCoord
end SelectedEntrySignedBox

end Aoyagi
end DLN
end DLNFibre
