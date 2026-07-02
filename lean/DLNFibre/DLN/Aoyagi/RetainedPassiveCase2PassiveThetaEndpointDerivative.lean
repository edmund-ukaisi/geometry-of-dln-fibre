import Mathlib.Analysis.Calculus.FDeriv.Prod
import DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaCFieldReadout
import DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure

/-!
# Case 2 with-following endpoint active-readout derivative

This file records the elementary derivative determinant of the source-type
active readout of the enlarged Case 2 endpoint map.  The determinant belongs
to the endomorphism
`endpointTopologyTupleActiveReadout n e ∘
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple`,
not to the bare endpoint topology-tuple map.  It is only finite-dimensional
coordinate calculus: no change-of-variables theorem, Haar/reference-image
identification, normal-crossing statement, pole order, or RLCT extraction is
proved here.
-/

noncomputable section

open scoped Matrix.Norms.Operator

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

namespace Case2PassiveThetaWithFollowingFactor

set_option linter.style.longLine false in
/-- The formal derivative of the source-side active selected-entry chart map:
identity on passive fields and the following factor, and the selected-entry
chart derivative on the active center coordinates. -/
noncomputable def activeSelectedEntryChartMapFDeriv
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
    Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →L[ℝ]
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
  ContinuousLinearMap.prodMap
    (ContinuousLinearMap.prodMap
      (ContinuousLinearMap.id ℝ
        (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J))
      (SelectedEntrySignedBox.CenterCoord.chartMapFDeriv
        (case2PassiveThetaPivotNext n hS hnext) z.1.2))
    (ContinuousLinearMap.id ℝ
      (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ))

set_option linter.style.longLine false in
/-- The source-side active selected-entry chart map has the expected product
derivative. -/
theorem hasFDerivAt_activeSelectedEntryChartMap
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
    HasFDerivAt
      (fun z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J =>
        ((z.1.1,
          SelectedEntrySignedBox.CenterCoord.chartMap
            (case2PassiveThetaPivotNext n hS hnext) z.1.2), z.2))
      (activeSelectedEntryChartMapFDeriv (ρ := ρ) (τ := τ) n hS hnext z) z := by
  let pivotNext := case2PassiveThetaPivotNext n hS hnext
  let Passive :=
    Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J
  let Center := Case2PassiveTheta.Center n S J → ℝ
  let Following := Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ
  have hPassive : HasFDerivAt (fun p : Passive => p)
      (ContinuousLinearMap.id ℝ Passive) z.1.1 := by
    simpa using hasFDerivAt_id (𝕜 := ℝ) z.1.1
  have hChart : HasFDerivAt
      (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
      (SelectedEntrySignedBox.CenterCoord.chartMapFDeriv pivotNext z.1.2) z.1.2 :=
    SelectedEntrySignedBox.CenterCoord.hasFDerivAt_chartMap pivotNext z.1.2
  have hTheta : HasFDerivAt
      (Prod.map (fun p : Passive => p)
        (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext))
      (ContinuousLinearMap.prodMap
        (ContinuousLinearMap.id ℝ Passive)
        (SelectedEntrySignedBox.CenterCoord.chartMapFDeriv pivotNext z.1.2))
      z.1 := by
    simpa [Passive, Center, pivotNext] using
      HasFDerivAt.prodMap z.1 hPassive hChart
  have hFollowing : HasFDerivAt (fun F : Following => F)
      (ContinuousLinearMap.id ℝ Following) z.2 := by
    simpa using hasFDerivAt_id (𝕜 := ℝ) z.2
  simpa [activeSelectedEntryChartMapFDeriv, Passive, Center, Following, pivotNext] using
    HasFDerivAt.prodMap z hTheta hFollowing

set_option linter.style.longLine false in
/-- The absolute determinant of the source-side active selected-entry chart
derivative is exactly the selected-entry source density. -/
theorem activeSelectedEntryChartMapFDeriv_absDet_eq_sourceDensity
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
    |LinearMap.det
      ((activeSelectedEntryChartMapFDeriv (ρ := ρ) (τ := τ) n hS hnext z :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →L[ℝ]
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →ₗ[ℝ]
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)| =
      SelectedEntrySignedBox.CenterCoord.sourceDensity
        (case2PassiveThetaPivotNext n hS hnext) z.1.2 := by
  let pivotNext := case2PassiveThetaPivotNext n hS hnext
  let Passive :=
    Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J
  let Center := Case2PassiveTheta.Center n S J → ℝ
  let Following := Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ
  have hinner :
      LinearMap.det
        (((ContinuousLinearMap.id ℝ Passive).prodMap
          (SelectedEntrySignedBox.CenterCoord.chartMapFDeriv pivotNext z.1.2) :
            Passive × Center →L[ℝ] Passive × Center) :
          Passive × Center →ₗ[ℝ] Passive × Center) =
        LinearMap.det ((ContinuousLinearMap.id ℝ Passive : Passive →L[ℝ] Passive) :
            Passive →ₗ[ℝ] Passive) *
          LinearMap.det
            ((SelectedEntrySignedBox.CenterCoord.chartMapFDeriv pivotNext z.1.2 :
              Center →L[ℝ] Center) : Center →ₗ[ℝ] Center) := by
    exact linearMap_det_prodMap_eq_mul
      ((ContinuousLinearMap.id ℝ Passive : Passive →L[ℝ] Passive) :
        Passive →ₗ[ℝ] Passive)
      ((SelectedEntrySignedBox.CenterCoord.chartMapFDeriv pivotNext z.1.2 :
        Center →L[ℝ] Center) : Center →ₗ[ℝ] Center)
  have houter :
      LinearMap.det
        ((((ContinuousLinearMap.id ℝ Passive).prodMap
          (SelectedEntrySignedBox.CenterCoord.chartMapFDeriv pivotNext z.1.2)).prodMap
            (ContinuousLinearMap.id ℝ Following) :
            (Passive × Center) × Following →L[ℝ] (Passive × Center) × Following) :
          (Passive × Center) × Following →ₗ[ℝ] (Passive × Center) × Following) =
        LinearMap.det
          (((ContinuousLinearMap.id ℝ Passive).prodMap
            (SelectedEntrySignedBox.CenterCoord.chartMapFDeriv pivotNext z.1.2) :
              Passive × Center →L[ℝ] Passive × Center) :
            Passive × Center →ₗ[ℝ] Passive × Center) *
          LinearMap.det ((ContinuousLinearMap.id ℝ Following :
            Following →L[ℝ] Following) : Following →ₗ[ℝ] Following) := by
    exact linearMap_det_prodMap_eq_mul
      (((ContinuousLinearMap.id ℝ Passive).prodMap
        (SelectedEntrySignedBox.CenterCoord.chartMapFDeriv pivotNext z.1.2) :
          Passive × Center →L[ℝ] Passive × Center) :
        Passive × Center →ₗ[ℝ] Passive × Center)
      ((ContinuousLinearMap.id ℝ Following : Following →L[ℝ] Following) :
        Following →ₗ[ℝ] Following)
  calc
    |LinearMap.det
      ((activeSelectedEntryChartMapFDeriv (ρ := ρ) (τ := τ) n hS hnext z :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →L[ℝ]
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →ₗ[ℝ]
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)| =
        |LinearMap.det
          ((SelectedEntrySignedBox.CenterCoord.chartMapFDeriv pivotNext z.1.2 :
            Center →L[ℝ] Center) : Center →ₗ[ℝ] Center)| := by
          rw [show
            LinearMap.det
              ((activeSelectedEntryChartMapFDeriv (ρ := ρ) (τ := τ) n hS hnext z :
                Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →L[ℝ]
                  Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
                Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →ₗ[ℝ]
                  Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) =
              LinearMap.det
                ((((ContinuousLinearMap.id ℝ Passive).prodMap
                  (SelectedEntrySignedBox.CenterCoord.chartMapFDeriv pivotNext z.1.2)).prodMap
                    (ContinuousLinearMap.id ℝ Following) :
                    (Passive × Center) × Following →L[ℝ]
                      (Passive × Center) × Following) :
                    (Passive × Center) × Following →ₗ[ℝ]
                      (Passive × Center) × Following) by
              simp [activeSelectedEntryChartMapFDeriv, Passive, Following, pivotNext]]
          rw [houter, hinner]
          simp [LinearMap.det_id]
    _ = SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext z.1.2 :=
      (SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_abs_chartMapFDeriv_det
        pivotNext z.1.2).symm

set_option linter.style.longLine false in
/-- The Frechet derivative of the source-side active selected-entry chart map
is the product derivative recorded above. -/
theorem fderiv_activeSelectedEntryChartMap
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
    fderiv ℝ
      (fun z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J =>
        ((z.1.1,
          SelectedEntrySignedBox.CenterCoord.chartMap
            (case2PassiveThetaPivotNext n hS hnext) z.1.2), z.2)) z =
      activeSelectedEntryChartMapFDeriv (ρ := ρ) (τ := τ) n hS hnext z :=
  (hasFDerivAt_activeSelectedEntryChartMap (ρ := ρ) (τ := τ) n hS hnext z).fderiv

set_option linter.style.longLine false in
set_option linter.unusedFintypeInType false in
/-- After applying the endpoint active readout, the enlarged Case 2 endpoint
map has source-side derivative determinant equal to the selected-entry source
density.  This is a statement about the source-type endomorphism
`endpointTopologyTupleActiveReadout n e ∘
case2PassiveThetaWithFollowingFactorEndpointTopologyTuple`, not about the bare
endpoint topology-tuple map. -/
theorem fderiv_endpointTopologyTupleActiveReadout_comp_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_absDet_eq_sourceDensity
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e
    let R :
        TopologyTuple ρ κ' ℝ →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      endpointTopologyTupleActiveReadout (ρ := ρ) (τ := τ) n e
    |LinearMap.det
      ((fderiv ℝ (fun z ↦ R (Y z)) z :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →L[ℝ]
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →ₗ[ℝ]
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)| =
      SelectedEntrySignedBox.CenterCoord.sourceDensity
        (case2PassiveThetaPivotNext n hS hnext) z.1.2 := by
  intro Y R
  let active :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
    fun z ↦
      ((z.1.1,
        SelectedEntrySignedBox.CenterCoord.chartMap
          (case2PassiveThetaPivotNext n hS hnext) z.1.2), z.2)
  have hfun : (fun z ↦ R (Y z)) = active := by
    funext w
    simpa [Y, R, active, Case2PassiveTheta.yNext] using
      endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext w eNext e
  rw [hfun]
  rw [show fderiv ℝ active z =
      activeSelectedEntryChartMapFDeriv (ρ := ρ) (τ := τ) n hS hnext z by
    simpa [active] using
      fderiv_activeSelectedEntryChartMap (ρ := ρ) (τ := τ) n hS hnext z]
  exact activeSelectedEntryChartMapFDeriv_absDet_eq_sourceDensity
    (ρ := ρ) (τ := τ) n hS hnext z

end Case2PassiveThetaWithFollowingFactor

end Aoyagi
end DLN
end DLNFibre
