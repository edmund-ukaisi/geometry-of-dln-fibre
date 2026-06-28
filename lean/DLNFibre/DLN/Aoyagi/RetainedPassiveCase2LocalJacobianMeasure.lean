import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure

/-!
# Retained-passive Case 2 local Jacobian-measure bridge

This file composes the two-edge Case 2 retained-passive selected-entry product
adapter with the canonical p.13 chart residual square-sum readout.  It is a
leaf bridge: the displayed Case 2 factor identities and entrywise readout stay
explicit, and no longer-suffix, positivity, integrability, normal-crossing, or
RLCT statement is proved here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- In the two-edge retained-passive Case 2 lane, the displayed post-pivot
factor identities and entrywise selected-entry product readout imply the
canonical p.13 chart-side selected-entry residual square-sum.

This removes only the selected-entry residual-factor matrix hypothesis from the
canonical chart square-sum bridge.  The displayed factor identities and
entrywise readout remain explicit, and the result is specialized to `M = 1`. -/
theorem aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_entrywise
    (W : Fin (1 + 2) → Type v) [∀ i, AddCommGroup (W i)]
    [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
    [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
    [∀ i, ContinuousSMul ℝ (W i)]
    (B : ∀ i : Fin (1 + 1), W i.succ →ₗ[ℝ] W i.castSucc)
    [∀ j, FiniteDimensional ℝ (W j)]
    {ι τ : Type*} [DecidableEq ι]
    {center : Finset ι} (pivot : center)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (z :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ)
    (hz :
      z ∈ topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (y : center → ℝ)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0) ≃ center)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last 2))
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (1 : Fin 3))
    (e₀ : τ ≃
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
    (hD :
      (show Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (1 : Fin 3)) ℝ from
        by
          simpa using
            (ofTopologyTuple
              (M := 1) (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) z).C (1 : Fin 2)).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (1 : Fin 3))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) ℝ from
        by
          simpa using
            (ofTopologyTuple
              (M := 1) (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀) z).C (0 : Fin 2)).submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
    (hentry :
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv (e₂ i, e₀ t))) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀
    let EFam := ∀ p : Fin (1 + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ
    let sourceChart : TopologyTuple ρ κ' ℝ → EFam :=
      fun y ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))
    aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ (fun E : EFam ↦ E)
          (sourceChart
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))) =
      SelectedEntrySignedBox.CenterCoord.residual pivot y := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀
  have hfactor :
      ChartLocalSuffixState.residualFactorProduct
          (ofTopologyTuple (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ') z).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c)) := by
    simpa [ρ, κ'] using
      residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
        (ρ := ρ) (τ := τ) (ι := ι) (κ := κ') (center := center)
        pivot n hS hcont residual Cprime z y residualCoordEquiv e₂ e₁ e₀
        hD hF hentry
  exact
    aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_residualFactorProduct_eq_matrix
      (M := 1) (W := W) (B := B) pivot z hz y residualCoordEquiv hfactor

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
