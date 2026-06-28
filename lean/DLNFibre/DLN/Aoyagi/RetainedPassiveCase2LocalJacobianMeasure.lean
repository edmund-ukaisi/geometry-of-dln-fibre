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

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 retained-passive data give the
fixed-base source-family local-source and source-readback matrix inputs.

This is a two-edge fixed-base wrapper.  It defines the source chart from the
transported retained-passive datum itself, so the local-source realization is
handled by `..._of_sourceEdgeFamilyOfData`; the endpoint-transported stored-`C`
readout supplies the selected-entry matrix hypothesis. -/
theorem retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := Fin (Module.finrank ℝ U₀))
          n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : (center → ℝ) → EdgeFamily :=
      fun yNext ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData yNext)
    (∀ yNext : center → ℝ,
      sourceChart yNext ∈
        paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
          (fun E : EdgeFamily ↦ E)) ∧
    (∀ yNext : center → ℝ,
      let E :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (sourceChart yNext p :
              reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
      ChartLocalSuffixState.residualFactorProduct
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
              (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
                n S (J + 1) (e (Fin.last 2)).symm
                ((e 0).symm.trans eNext) c))) := by
  intro center pivotNext EdgeFamily retainedData sourceChart
  exact
    retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_sourceEdgeFamilyOfData
      (M := 1) (W := W₂) (B := B₂) (pivot := pivotNext)
      (U₀ := U₀) (hU₀ := hU₀)
      (retainedData := retainedData)
      (hdet := fun yNext ↦ by
        simpa [retainedData] using
          case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
            (ρ := Fin (Module.finrank ℝ U₀))
            n hS hcont hnext yNext eNext e)
      (residualCoordEquiv :=
        case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
          n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext))
      (hdataFactor := fun yNext ↦ by
        simpa [retainedData] using
          case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
            (ρ := Fin (Module.finrank ℝ U₀))
            n hS hcont hnext yNext eNext e)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 retained-passive data give the
fixed-base selected-entry residual square-sum readout.

This is the residual-square-sum corollary of
`..._of_case2EndpointTransport_sourceEdgeFamilyOfData`.  It still uses supplied
endpoint equivalences and does not assert any measure, Jacobian, normal-crossing,
pole-order, or RLCT consequence. -/
theorem aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_case2EndpointTransport_sourceEdgeFamilyOfData
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := Fin (Module.finrank ℝ U₀))
          n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : (center → ℝ) → EdgeFamily :=
      fun yNext ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData yNext)
    ∀ yNext : center → ℝ,
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart yNext)) =
        SelectedEntrySignedBox.CenterCoord.residual pivotNext yNext := by
  intro center pivotNext EdgeFamily retainedData sourceChart
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
  have hpre :
      (∀ yNext : center → ℝ,
        sourceChart yNext ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E)) ∧
      (∀ yNext : center → ℝ,
        let E :=
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              (sourceChart yNext p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
        ChartLocalSuffixState.residualFactorProduct
            (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E).C
            (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
          AoyagiResidualBlockCoordinateIndex.matrix
            (fun c ↦
              SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
                (residualCoordEquiv c))) := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
      residualCoordEquiv] using
      retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
  exact
    aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_sourceReadback_residualFactorProduct_eq_matrix
      (M := 1) (W := W₂) (B := B₂) (pivot := pivotNext)
      (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EdgeFamily ↦ E)
      sourceChart residualCoordEquiv hpre.2

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

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- In the two-edge retained-passive Case 2 lane, a supplied nonzero selected
pivot for the displayed post-pivot product gives selected-entry coordinates
whose residual is the canonical p.13 chart-side square-sum.

This is the pivot-nonzero variant of
`aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_entrywise`.
It still does not prove the selected pivot is nonzero or construct source
production. -/
theorem exists_aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_pivot_ne_zero
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
    (hpivot :
      let productCoordEquiv :
          AoyagiResidualBlockCoordinateIndex
              (Case2ResidualRowIndex n S (J + 1)) τ ≃ center :=
        (Equiv.prodCongr e₂ e₀).trans residualCoordEquiv
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
        (productCoordEquiv.symm pivot).1 (productCoordEquiv.symm pivot).2 ≠ 0) :
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
    ∃ y : center → ℝ,
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
  rcases
    exists_residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_pivot_ne_zero
      (ρ := ρ) (τ := τ) (ι := ι) (κ := κ') (center := center)
      pivot n hS hcont residual Cprime z residualCoordEquiv e₂ e₁ e₀ hD hF hpivot with
    ⟨y, hfactor⟩
  refine ⟨y, ?_⟩
  exact
    aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_residualFactorProduct_eq_matrix
      (M := 1) (W := W) (B := B) pivot z hz y residualCoordEquiv hfactor

set_option maxRecDepth 2048 in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- In the two-edge retained-passive Case 2 lane, a nonzero displayed
post-pivot product matrix gives some selected-entry pivot and coordinates whose
residual is the canonical p.13 chart-side square-sum.

This is the all-pivot finite selected-entry variant of
`exists_aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_pivot_ne_zero`.
It still assumes nonzeroness of the displayed product and does not construct
source production. -/
theorem exists_pivot_aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_of_ne_zero
    (W : Fin (1 + 2) → Type v) [∀ i, AddCommGroup (W i)]
    [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
    [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
    [∀ i, ContinuousSMul ℝ (W i)]
    (B : ∀ i : Fin (1 + 1), W i.succ →ₗ[ℝ] W i.castSucc)
    [∀ j, FiniteDimensional ℝ (W j)]
    {ι τ : Type*} [DecidableEq ι]
    {center : Finset ι}
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
    (hprod :
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime ≠ 0) :
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
    ∃ pivot : center, ∃ y : center → ℝ,
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
  rcases
    exists_pivot_residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero
      (ρ := ρ) (τ := τ) (ι := ι) (κ := κ') (center := center)
      n hS hcont residual Cprime z residualCoordEquiv e₂ e₁ e₀ hD hF hprod with
    ⟨pivot, y, hfactor⟩
  refine ⟨pivot, y, ?_⟩
  exact
    aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_residualFactorProduct_eq_matrix
      (M := 1) (W := W) (B := B) pivot z hz y residualCoordEquiv hfactor

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
