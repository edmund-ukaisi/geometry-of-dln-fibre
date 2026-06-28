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
/-- The raw-order p.13 source chart of the topology tuple attached to the
endpoint-transported explicit Case 2 datum is the direct fixed-base p.13
source edge family of that datum.

This is a source-family presentation identity only.  It is not endpoint
provenance, source-image equality, pushforward-measure transport, source-rank
coverage, a Jacobian comparison, normal crossings, pole order, or RLCT
extraction. -/
theorem paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_case2EndpointTransport_sourceEdgeFamilyOfData
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
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ) :
    let data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext yNext eNext).endpointTransport e
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W₂ B₂ U₀ hU₀
        (topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (topologyTuple data)) =
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W₂ B₂ U₀ hU₀
        data := by
  intro data
  exact
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
      (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) data
      (by
        simpa [data] using
          case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
            (ρ := Fin (Module.finrank ℝ U₀))
            n hS hcont hnext yNext eNext e)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The fixed-base source readback of the endpoint-transported explicit Case 2
source edge family recovers the transported retained-passive datum. -/
theorem sourceReadback_eq_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_of_case2EndpointTransport_sourceEdgeFamilyOfData
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
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ) :
    let data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : ∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        W₂ B₂ U₀ hU₀ data
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (sourceChart p :
            reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
      data := by
  intro data sourceChart E
  have hdet : data.detChart := by
    simpa [data] using
      case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext yNext eNext e
  have hedge : E = data.edgeMatrix := by
    simpa [E, sourceChart] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
        (K := ℝ) (M := 1) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) data
  rw [hedge]
  exact
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_edgeMatrix_eq
      (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) (data := data) hdet

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The `C 1` factor of the fixed-base source readback for the
endpoint-transported explicit Case 2 source edge family is the displayed
post-pivot residual block after reindexing by the forward endpoint
equivalences. -/
theorem sourceReadback_C_one_submatrix_eq_displayedPostPivotResidualBlock_of_case2EndpointTransport_sourceEdgeFamilyOfData
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
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ) :
    let data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : ∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        W₂ B₂ U₀ hU₀ data
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (sourceChart p :
            reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    let read :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E
    (show Matrix
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (1 : Fin 3)) ℝ from
      by simpa using read.C (1 : Fin 2)).submatrix
        (e (Fin.last 2)) (e (1 : Fin 3)) =
      case2DisplayedPostPivotResidualBlock n hS hcont
        (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext) := by
  intro data sourceChart E read
  have hread : read = data := by
    simpa [data, sourceChart, E, read] using
      sourceReadback_eq_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_of_case2EndpointTransport_sourceEdgeFamilyOfData
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e yNext
  rw [hread]
  simpa [data] using
    case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_one_submatrix_eq_displayedPostPivotResidualBlock
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext yNext eNext e

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The `C 0` factor of the fixed-base source readback for the
endpoint-transported explicit Case 2 source edge family is the displayed free
following factor after reindexing by the forward endpoint equivalences. -/
theorem sourceReadback_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor_of_case2EndpointTransport_sourceEdgeFamilyOfData
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
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ) :
    let data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : ∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        W₂ B₂ U₀ hU₀ data
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (sourceChart p :
            reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    let read :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E
    (show Matrix
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (1 : Fin 3))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ℝ from
      by simpa using read.C (0 : Fin 2)).submatrix
        (e (1 : Fin 3)) (e 0) =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont
        (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext) := by
  intro data sourceChart E read
  have hread : read = data := by
    simpa [data, sourceChart, E, read] using
      sourceReadback_eq_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_of_case2EndpointTransport_sourceEdgeFamilyOfData
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e yNext
  rw [hread]
  simpa [data] using
    case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext yNext eNext e

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The fixed-base source readback for the endpoint-transported explicit Case 2
source edge family has the displayed successor pivot as its actual
selected-entry product coordinate. -/
theorem sourceReadback_residualFactorProduct_fixedPivot_entry_eq_yNext_of_case2EndpointTransport_sourceEdgeFamilyOfData
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
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ) :
    let data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : ∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        W₂ B₂ U₀ hU₀ data
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (sourceChart p :
            reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    let read :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E
    let pivotNext :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩
    let residualCoordEquiv :
        AoyagiResidualBlockCoordinateIndex
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃
          (case2ResidualBlockPivotEntries n S (J + 1) : Type) :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    AoyagiResidualBlockCoordinateIndex.value
        (ChartLocalSuffixState.residualFactorProduct
          read.C (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)))
        (residualCoordEquiv.symm pivotNext) =
      yNext pivotNext := by
  intro data sourceChart E read pivotNext residualCoordEquiv
  have hread : read = data := by
    simpa [data, sourceChart, E, read] using
      sourceReadback_eq_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_of_case2EndpointTransport_sourceEdgeFamilyOfData
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e yNext
  rw [hread]
  simpa [data, pivotNext, residualCoordEquiv] using
    case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_fixedPivot_entry_eq_yNext
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext yNext eNext e

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The fixed-base source readback for the endpoint-transported explicit Case 2
source edge family has a nonzero fixed successor-pivot product coordinate when
the supplied successor pivot coordinate is nonzero. -/
theorem sourceReadback_residualFactorProduct_fixedPivot_entry_ne_zero_of_case2EndpointTransport_sourceEdgeFamilyOfData_yNext_pivot_ne_zero
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
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (hyNext :
      yNext (⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0) :
    let data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext yNext eNext).endpointTransport e
    let sourceChart : ∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        W₂ B₂ U₀ hU₀ data
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (sourceChart p :
            reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    let read :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E
    let pivotNext :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩
    let residualCoordEquiv :
        AoyagiResidualBlockCoordinateIndex
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃
          (case2ResidualBlockPivotEntries n S (J + 1) : Type) :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    AoyagiResidualBlockCoordinateIndex.value
        (ChartLocalSuffixState.residualFactorProduct
          read.C (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)))
        (residualCoordEquiv.symm pivotNext) ≠ 0 := by
  intro data sourceChart E read pivotNext residualCoordEquiv
  rw [
    sourceReadback_residualFactorProduct_fixedPivot_entry_eq_yNext_of_case2EndpointTransport_sourceEdgeFamilyOfData
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e yNext]
  exact hyNext

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
/-- Self-endpoint specialization of the Case 2 endpoint-transported fixed-base
source-family inputs.

Here the free right endpoint is chosen to be the successor residual-column
index, so the `eNext` argument of the general theorem is `Equiv.refl _`.  The
endpoint-family equivalences `e` are still supplied. -/
theorem retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_selfEndpoint_sourceEdgeFamilyOfData
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J
            (Case2ResidualColIndex n S (J + 1)) q ≃
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
          n hS hcont hnext yNext
          (Equiv.refl (Case2ResidualColIndex n S (J + 1)))).endpointTransport e
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
                ((e 0).symm.trans
                  (Equiv.refl (Case2ResidualColIndex n S (J + 1)))) c))) := by
  intro center pivotNext EdgeFamily retainedData sourceChart
  simpa [retainedData, sourceChart] using
    retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
      (Equiv.refl (Case2ResidualColIndex n S (J + 1))) e

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Cardinality equalities supply the endpoint equivalences for the Case 2
endpoint-transported fixed-base source-family local-source and source-readback
matrix inputs.

The equivalences are the noncanonical finite equivalences produced by
`case2EndpointTransportEquivs_of_card_eq`.  This theorem does not prove the
cardinality equalities or add source-prior, Jacobian, normal-crossing, pole
order, or RLCT content. -/
theorem retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_card_eq
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
    (hNext :
      Fintype.card τ =
        Fintype.card (Case2ResidualColIndex n S (J + 1)))
    (hEndpoints :
      ∀ q : Fin 3,
        Fintype.card (case2PostPivotTwoEdgeDomain n S J τ q) =
          Fintype.card
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let equivs :=
      case2EndpointTransportEquivs_of_card_eq
        (κ := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
        n S J hNext hEndpoints
    let eNext := equivs.1
    let e := equivs.2
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
  intro center pivotNext EdgeFamily equivs eNext e retainedData sourceChart
  simpa [equivs, eNext, e, retainedData, sourceChart] using
    retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) equivs.1 equivs.2

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

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The endpoint-transported explicit Case 2 retained-passive source chart is
continuous as a finite selected-entry coordinate map.

This proves only regularity of the chart-produced fixed-base source family.  It
does not construct the endpoint equivalences, compare source priors or
Jacobians, prove normal crossings, or extract RLCT. -/
theorem continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
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
    Continuous sourceChart := by
  intro center EdgeFamily retainedData sourceChart
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ : Fin 3 → Type := case2PostPivotTwoEdgeDomain n S J τ
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let transportedData :
      (center → ℝ) →
        {data :
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := ρ) κ' // data.detChart} :=
    fun yNext ↦
      ⟨retainedData yNext, by
        simpa [retainedData, ρ, κ'] using
          case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
            (ρ := ρ) n hS hcont hnext yNext eNext e⟩
  have hselected :
      Continuous
        (fun yNext : center → ℝ ↦
          (⟨case2PostPivotSelectedEntryRetainedPassiveData
              (ρ := ρ) n hS hcont hnext yNext eNext,
            case2PostPivotSelectedEntryRetainedPassiveData_detChart
              (ρ := ρ) n hS hcont hnext yNext eNext⟩ :
            {data :
              ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
                (K := ℝ) (ρ := ρ) κ // data.detChart})) := by
    simpa [center, ρ, κ] using
      continuous_case2PostPivotSelectedEntryRetainedPassiveData_detChart_subtype
        (ρ := ρ) n hS hcont hnext eNext
  have htransport :
      Continuous
        (fun data :
            {data :
              ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
                (K := ℝ) (ρ := ρ) κ // data.detChart} ↦
          (⟨data.1.endpointTransport e,
            (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.endpointTransport_detChart
              (K := ℝ) (ρ := ρ) e data.1).2 data.2⟩ :
            {data :
              ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
                (K := ℝ) (ρ := ρ) κ' // data.detChart})) := by
    simpa [κ, κ'] using
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport_detChart_subtype
        (K := ℝ) (ρ := ρ) e
  have htransported : Continuous transportedData := by
    simpa [transportedData, retainedData, ρ, κ, κ'] using htransport.comp hselected
  have hsource :
      Continuous
        (fun data :
            {data :
              ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
                (K := ℝ) (ρ := ρ) κ' // data.detChart} ↦
          paperEndpointFixedBaseRetainedPassiveP13SourceChart W₂ B₂ U₀ hU₀ data) :=
    continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
      (K := ℝ) W₂ B₂ U₀ hU₀
  simpa [sourceChart, retainedData, transportedData,
    paperEndpointFixedBaseRetainedPassiveP13SourceChart,
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData, ρ, κ'] using
    hsource.comp htransported

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 retained-passive data give the
chart-produced selected-entry local finite-integral handoff.

The source measure here is the pushforward of the selected-entry signed-box
measure by the displayed endpoint-transported source chart.  This does not
identify an external/original source prior, compare Jacobians for such a prior,
construct endpoint equivalences, prove normal crossings, compute pole order, or
extract RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
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
    let base : EdgeFamily :=
      fun p ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
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
    let rhoReg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
    ∀ {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ},
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀ base (fun E : EdgeFamily ↦ E) H r rEdge →
    ∀ {ν : Measure (EuclideanSpace ℝ rhoReg)}, ν.IsAddHaarMeasure →
    ∀ {loss density : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ}
      {t Rreg creg Creg : ℝ} {Rres : center → ℝ},
      0 < Rreg → 0 < creg → 0 ≤ Creg → 0 < t →
      (∀ i, 0 < Rres i) →
      2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E)),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rreg →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E)),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rreg →
            0 ≤ density (x, u)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E)),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rreg →
            density (x, u) ≤ Creg) →
      let sourceMeasure :=
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let μ := Measure.map sourceChart sourceMeasure
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
      ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
        (∫⁻ z : EdgeFamily × EuclideanSpace ℝ rhoReg,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rreg).indicator
              (fun u =>
                (loss (z.1, u)) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg _ _ _
    H r rEdge sourceData ν hν loss density t Rreg creg Creg Rres
    hRreg hcreg hCreg ht hRres hcrit_pivot hloss hdensity_nonneg hdensity_le
    sourceMeasure μ sourceStratum
  letI : ν.IsAddHaarMeasure := hν
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
  have hsourceChart :
      AEMeasurable sourceChart
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))) := by
    exact
      (continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e).aemeasurable
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceReadback_residualFactorProduct_eq_matrix_chartProducedMeasure
      (M := 1) (W := W₂) (B := B₂) (pivot := pivotNext)
      (x₀ := base) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EdgeFamily ↦ E)
      (H := H) (r := r) (rEdge := rEdge)
      sourceData (ν := ν) (sourceChart := sourceChart)
      (loss := loss) (density := density)
      (t := t) (Rreg := Rreg) (creg := creg) (Creg := Creg)
      (Rres := Rres)
      hRreg hcreg hCreg ht
      (by simpa [EdgeFamily] using (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
      (by rfl)
      hsourceChart hpre.1 hRres hcrit_pivot residualCoordEquiv hpre.2
      hloss hdensity_nonneg hdensity_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 chart-produced finite-integral
handoff for a positive continuous density factor.

This is the radius-shrinking version of
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure`:
continuity and positivity of the transported density at `(base,0)` produce
local nonnegativity and boundedness after shrinking the regular-coordinate
radius.  It does not identify an external/original source prior, compare
Jacobians for such a prior, construct endpoint equivalences, prove normal
crossings, compute pole order, or extract RLCT. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density
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
    let base : EdgeFamily :=
      fun p ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
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
    let rhoReg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
        (fun E : EdgeFamily ↦ E)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
    ∀ {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ},
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀ base (fun E : EdgeFamily ↦ E) H r rEdge →
    ∀ {ν : Measure (EuclideanSpace ℝ rhoReg)}, ν.IsAddHaarMeasure →
    ∀ {loss density : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ}
      {t Rmax creg : ℝ} {Rres : center → ℝ},
      0 < Rmax → 0 < creg → 0 < t →
      (∀ i, 0 < Rres i) →
      2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
      ContinuousAt density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      0 < density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      (∀ᶠ x in nhdsWithin base localSource,
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rmax →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) →
      let sourceMeasure :=
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let μ := Measure.map sourceChart sourceMeasure
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
      ∃ R C : ℝ, ∃ U : Set EdgeFamily,
        0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ base ∈ U ∧
        (∫⁻ z : EdgeFamily × EuclideanSpace ℝ rhoReg,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ rhoReg) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg localSource _ _ _
    H r rEdge sourceData ν hν loss density t Rmax creg Rres
    hRmax hcreg ht hRres hcrit_pivot hdensity_cont hdensity_pos hloss
    sourceMeasure μ sourceStratum
  rcases
      exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
        (α := EdgeFamily) (E := EuclideanSpace ℝ rhoReg)
        (density := density) (x₀ := base) (s := localSource) (Rmax := Rmax)
        hdensity_cont hdensity_pos hRmax with
    ⟨R, C, hR, hRle, hC, hdensity_nonneg, hdensity_le⟩
  have hlossR :
      ∀ᶠ x in nhdsWithin base localSource,
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) R →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u) := by
    filter_upwards [hloss] with x hx u hu
    exact hx u (Metric.ball_subset_ball hRle hu)
  rcases
      exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (H := H) (r := r) (rEdge := rEdge) sourceData (ν := ν) hν
        (loss := loss) (density := density)
        (t := t) (Rreg := R) (creg := creg) (Creg := C) (Rres := Rres)
        hR hcreg hC ht hRres hcrit_pivot hlossR hdensity_nonneg hdensity_le with
    ⟨U, hUopen, hbaseU, hfinite⟩
  exact ⟨R, C, U, hR, hRle, hC, hUopen, hbaseU, hfinite⟩

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
