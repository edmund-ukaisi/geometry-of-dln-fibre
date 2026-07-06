import DLNFibre.DLN.Aoyagi.EndpointLossComparison
import DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure

/-!
# Retained-passive Case 2 local Jacobian-measure bridge

This file composes the two-edge Case 2 retained-passive selected-entry product
adapter with the canonical p.13 chart residual square-sum readout.  It is a
leaf bridge: the displayed Case 2 factor identities and entrywise readout stay
explicit.  The positivity and finite-integral statements in this file are
chart-produced or domination-based local handoffs; no longer-suffix, exact
localized residual marginal, determinant-chart Haar/source-prior transport,
normal-crossing, or RLCT statement is proved here.
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
/-- The endpoint-transported explicit continuing Case 2 selected-entry source
family lies in Aoyagi's source-shaped rank stratum when the base-product rank
and the two intended edge-rank values are supplied explicitly.

The first edge rank is `r + card tau`; the second is `r` plus the rank of the
successor selected-entry matrix.  This is pointwise source-stratum membership,
not source-rank coverage, exact-rank openness, or a numerical successor-rank
theorem. -/
theorem case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum
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
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0)
    (hr1 :
      r + (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank =
        rEdge 1) :
    let data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext yNext eNext).endpointTransport e
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W₂ B₂ U₀ hU₀
        data ∈
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂
        (fun E : ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ ↦ E)
        r rEdge := by
  intro data
  let rawData :=
    case2PostPivotSelectedEntryRetainedPassiveData
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext yNext eNext
  have hdet : data.detChart := by
    simpa [data, rawData] using
      case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext yNext eNext e
  have hC0raw : (rawData.C (0 : Fin 2)).rank = Fintype.card τ := by
    simpa [rawData, case2PostPivotSelectedEntryRetainedPassiveData,
      case2PostPivotRetainedPassiveData, case2PostPivotFreeTwoEdgeFactorFamily,
      case2SuccessorSelectedEntrySourceCprime] using
      rank_case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfMatrix
        n hS hcont
        (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) eNext
  have hC1raw :
      (rawData.C (1 : Fin 2)).rank =
        (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank := by
    simpa [rawData, case2PostPivotSelectedEntryRetainedPassiveData,
      case2PostPivotRetainedPassiveData, case2PostPivotFreeTwoEdgeFactorFamily,
      case2SuccessorSelectedEntrySourceResidual] using
      rank_case2DisplayedPostPivotResidualBlock_sourceResidualOfMatrix
        n hS hcont
        (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) eNext
  have hC0 : (data.C (0 : Fin 2)).rank = Fintype.card τ := by
    calc
      (data.C (0 : Fin 2)).rank = (rawData.C (0 : Fin 2)).rank := by
        simpa [data, rawData] using
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_endpointTransport_C
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) e rawData (0 : Fin 2)
      _ = Fintype.card τ := hC0raw
  have hC1 :
      (data.C (1 : Fin 2)).rank =
        (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank := by
    calc
      (data.C (1 : Fin 2)).rank = (rawData.C (1 : Fin 2)).rank := by
        simpa [data, rawData] using
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_endpointTransport_C
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) e rawData (1 : Fin 2)
      _ = (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank := hC1raw
  refine
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank_add_eq
      (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) data hdet hprod ?_
  intro p
  fin_cases p
  · calc
      r + (data.C (0 : Fin 2)).rank = r + Fintype.card τ := by rw [hC0]
      _ = rEdge 0 := hr0
  · calc
      r + (data.C (1 : Fin 2)).rank =
          r + (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank := by
        rw [hC1]
      _ = rEdge 1 := hr1

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
/-- Passive-parameter endpoint-transported Case 2 retained-passive data give
the fixed-base source-family local-source and source-readback matrix inputs.

The source-chart domain is `η × (center → ℝ)`: `η` supplies the retained
passive fields and the selected-entry coordinates supply the residual `C`
family.  This is a source-map/readback bridge, not an image/coverage theorem,
measure pushforward, source-prior transport, normal-crossing statement, pole
order, or RLCT extraction. -/
theorem retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    (∀ z : η × (center → ℝ),
      sourceChart z ∈
        paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
          (fun E : EdgeFamily ↦ E)) ∧
    (∀ z : η × (center → ℝ),
      let E :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (sourceChart z p :
              reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
      ChartLocalSuffixState.residualFactorProduct
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
              (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
                n S (J + 1) (e (Fin.last 2)).symm
                ((e 0).symm.trans eNext) c))) := by
  intro center pivotNext EdgeFamily retainedData sourceChart
  constructor
  · intro z
    dsimp [paperEndpointFixedBaseRetainedPassiveP13LocalSource]
    rw [
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
        (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) (retainedData z)]
    exact
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart_edgeMatrix_of_detChart
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) (retainedData z)
        (by
          simpa [retainedData] using
            case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
              (ρ := Fin (Module.finrank ℝ U₀))
              n hS hcont hnext (A1passive z.1) (F2 z.1)
              (A3passive z.1) (Ctop z.1) (F3 z.1) z.2 eNext e
              (hCtop z.1) (hA1passive z.1))
  · intro z
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (sourceChart z p :
            reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    have hdet : (retainedData z).detChart := by
      simpa [retainedData] using
        case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
          (ρ := Fin (Module.finrank ℝ U₀))
          n hS hcont hnext (A1passive z.1) (F2 z.1)
          (A3passive z.1) (Ctop z.1) (F3 z.1) z.2 eNext e
          (hCtop z.1) (hA1passive z.1)
    have hedge :
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              ((fun E : EdgeFamily ↦ E) (sourceChart z) p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)) =
          (retainedData z).edgeMatrix := by
      simpa [sourceChart] using
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
          (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) (retainedData z)
    have hread :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
          retainedData z := by
      simpa [E] using
        sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq
          (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
          (Cedge := fun E : EdgeFamily ↦ E)
          (sourceChart z) (retainedData z) hdet hedge
    change
      ChartLocalSuffixState.residualFactorProduct
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
              (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
                n S (J + 1) (e (Fin.last 2)).symm
                ((e 0).symm.trans eNext) c))
    rw [hread]
    simpa [retainedData, pivotNext] using
      case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
        (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
        (F3 z.1) z.2 eNext e

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Passive-parameter endpoint-transported Case 2 source-family points lie in
the named source-rank stratum when the base-product rank and intended edge
ranks are supplied explicitly.

The passive fields enter the edge matrices, but the rank calculation is still
controlled by the stored `C` factors once the retained-passive determinant
chart is available.  This is pointwise source-stratum support only; it does not
prove source-rank coverage, source-image equality, source-prior transport,
Jacobian compatibility, normal crossings, pole order, or RLCT. -/
theorem case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    ∀ z : η × (center → ℝ),
      r + (case2SuccessorSelectedEntryMatrix n hS hnext z.2 eNext).rank =
        rEdge 1 →
      sourceChart z ∈
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E)
          r rEdge := by
  intro center EdgeFamily retainedData sourceChart z hr1
  let rawData :=
    case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
      (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
      (F3 z.1) z.2 eNext
  have hdet : (retainedData z).detChart := by
    simpa [retainedData, rawData] using
      case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
        (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
        (F3 z.1) z.2 eNext e (hCtop z.1) (hA1passive z.1)
  have hC0raw : (rawData.C (0 : Fin 2)).rank = Fintype.card τ := by
    simpa [rawData, case2PostPivotSelectedEntryRetainedPassiveDataWithPassive,
      case2PostPivotFreeTwoEdgeFactorFamily,
      case2SuccessorSelectedEntrySourceCprime] using
      rank_case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfMatrix
        n hS hcont (case2SuccessorSelectedEntryMatrix n hS hnext z.2 eNext) eNext
  have hC1raw :
      (rawData.C (1 : Fin 2)).rank =
        (case2SuccessorSelectedEntryMatrix n hS hnext z.2 eNext).rank := by
    simpa [rawData, case2PostPivotSelectedEntryRetainedPassiveDataWithPassive,
      case2PostPivotFreeTwoEdgeFactorFamily,
      case2SuccessorSelectedEntrySourceResidual] using
      rank_case2DisplayedPostPivotResidualBlock_sourceResidualOfMatrix
        n hS hcont (case2SuccessorSelectedEntryMatrix n hS hnext z.2 eNext) eNext
  have hC0 : ((retainedData z).C (0 : Fin 2)).rank = Fintype.card τ := by
    calc
      ((retainedData z).C (0 : Fin 2)).rank = (rawData.C (0 : Fin 2)).rank := by
        simpa [retainedData, rawData] using
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_endpointTransport_C
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) e rawData (0 : Fin 2)
      _ = Fintype.card τ := hC0raw
  have hC1 :
      ((retainedData z).C (1 : Fin 2)).rank =
        (case2SuccessorSelectedEntryMatrix n hS hnext z.2 eNext).rank := by
    calc
      ((retainedData z).C (1 : Fin 2)).rank = (rawData.C (1 : Fin 2)).rank := by
        simpa [retainedData, rawData] using
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_endpointTransport_C
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) e rawData (1 : Fin 2)
      _ = (case2SuccessorSelectedEntryMatrix n hS hnext z.2 eNext).rank := hC1raw
  refine
    paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank_add_eq
      (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) (retainedData z)
      hdet hprod ?_
  intro p
  fin_cases p
  · calc
      r + ((retainedData z).C (0 : Fin 2)).rank = r + Fintype.card τ := by rw [hC0]
      _ = rEdge 0 := hr0
  · calc
      r + ((retainedData z).C (1 : Fin 2)).rank =
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.2 eNext).rank := by
        rw [hC1]
      _ = rEdge 1 := hr1

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Passive-parameter endpoint-transported Case 2 source-family points have
residual-coordinate map equal to the selected-entry chart map.

This is the coordinate readout consequence of the passive source-readback
bridge.  It does not prove source-image equality, coverage, measure
pushforward, source-prior transport, normal crossings, pole order, or RLCT. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∀ z : η × (center → ℝ), ∀ c,
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
          (sourceChart z) c =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
          (residualCoordEquiv c) := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv z c
  have hpre :
      (∀ z : η × (center → ℝ),
        sourceChart z ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E)) ∧
      (∀ z : η × (center → ℝ),
        let E :=
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              (sourceChart z p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
        ChartLocalSuffixState.residualFactorProduct
            (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E).C
            (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
          AoyagiResidualBlockCoordinateIndex.matrix
            (fun c ↦
              SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
                (residualCoordEquiv c))) := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
      residualCoordEquiv] using
      retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3 hCtop hA1passive
  exact
    paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_sourceReadback_residualFactorProduct_eq_matrix
      (M := 1) (W := W₂) (B := B₂) (pivot := pivotNext)
      (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EdgeFamily ↦ E)
      (fun y : center → ℝ ↦ sourceChart (z.1, y))
      residualCoordEquiv
      (fun y ↦ by
        simpa using hpre.2 (z.1, y))
      z.2 c

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Passive-parameter endpoint-transported Case 2 source-family points lie in
the named source-rank stratum and p.13 local source, with residual coordinates
read back as the selected-entry chart map.

This is a pointwise support/readout package for constructed passive-sector
points.  The rank hypotheses are supplied for each selected-entry coordinate;
the theorem does not prove source-rank coverage, source-image equality,
source-prior transport, Jacobian compatibility, normal crossings, pole order,
or RLCT. -/
theorem case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∀ z : η × (center → ℝ),
      r + (case2SuccessorSelectedEntryMatrix n hS hnext z.2 eNext).rank =
        rEdge 1 →
        sourceChart z ∈
          paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E)
            r rEdge ∧
        sourceChart z ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E) ∧
        (∀ c,
          paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
              (sourceChart z) c =
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
              (residualCoordEquiv c)) := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv z hr1
  have hpre :
      (∀ z : η × (center → ℝ),
        sourceChart z ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E)) ∧
      (∀ z : η × (center → ℝ),
        let E :=
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              (sourceChart z p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
        ChartLocalSuffixState.residualFactorProduct
            (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E).C
            (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
          AoyagiResidualBlockCoordinateIndex.matrix
            (fun c ↦
              SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
                (residualCoordEquiv c))) := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
      residualCoordEquiv] using
      retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3 hCtop hA1passive
  have hstratum :
      sourceChart z ∈
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge := by
    simpa [center, EdgeFamily, retainedData, sourceChart] using
      case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3 hCtop hA1passive hprod hr0 z hr1
  refine ⟨hstratum, hpre.1 z, ?_⟩
  intro c
  have hcoord :=
    paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      A1passive F2 A3passive Ctop F3 hCtop hA1passive z c
  simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
    residualCoordEquiv] using hcoord

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The endpoint-transported passive-parameter Case 2 source chart is
continuous when the passive fields are continuous and the determinant-chart
unit hypotheses hold pointwise.

This proves regularity of the chart-produced fixed-base source family only. It
does not construct a product measure, source-image theorem, source-prior
transport, Jacobian formula, normal crossings, pole order, or RLCT. -/
theorem continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [TopologicalSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    Continuous sourceChart := by
  intro center EdgeFamily retainedData sourceChart
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ : Fin 3 → Type := case2PostPivotTwoEdgeDomain n S J τ
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let rawData :
      η × (center → ℝ) →
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) κ :=
    fun z ↦
      case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
        (ρ := ρ) n hS hcont hnext
        (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
        (F3 z.1) z.2 eNext
  let rawDetData :
      η × (center → ℝ) →
        {data :
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := ρ) κ // data.detChart} :=
    fun z ↦
      ⟨rawData z, by
        simpa [rawData, center, ρ, κ] using
          case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_detChart
            (ρ := ρ) n hS hcont hnext
            (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
            (F3 z.1) z.2 eNext (hCtop z.1) (hA1passive z.1)⟩
  let transportedData :
      η × (center → ℝ) →
        {data :
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := ρ) κ' // data.detChart} :=
    fun z ↦
      ⟨retainedData z, by
        simpa [retainedData, rawData, center, ρ, κ'] using
          case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
            (ρ := ρ) n hS hcont hnext
            (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
            (F3 z.1) z.2 eNext e (hCtop z.1) (hA1passive z.1)⟩
  have hraw : Continuous rawData := by
    simpa [rawData, center, ρ, κ] using
      continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
        (ρ := ρ) n hS hcont hnext
        A1passive F2 A3passive Ctop F3 eNext
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
  have hrawDet : Continuous rawDetData := by
    exact hraw.subtype_mk _
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
    simpa [transportedData, retainedData, rawDetData, rawData, ρ, κ, κ'] using
      htransport.comp hrawDet
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

set_option linter.style.longLine false in
/-- Along the endpoint-transported passive-parameter Case 2 selected-entry
chart, the retained-passive solved-`A1` product raw-order Jacobian density is
locally a positive bounded unit.

This is only passive Jacobian accounting for the chart coordinates.  It does
not prove source-prior transport, determinant-chart Haar transport,
source-image coverage, normal crossings, pole order, or RLCT. -/
theorem exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [TopologicalSpace η]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (z₀ : η × (case2ResidualBlockPivotEntries n S (J + 1) → ℝ))
    (hCtop₀ : IsUnit ((Ctop z₀.1).det))
    (hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let Y :
        η × (center → ℝ) →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦ topologyTuple (retainedData z)
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
      ∀ᶠ z in nhds z₀,
        ε ≤
            retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z) ∧
          retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z) ≤ K := by
  intro center retainedData Y
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ : Fin 3 → Type := case2PostPivotTwoEdgeDomain n S J τ
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let rawData :
      η × (center → ℝ) →
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) κ :=
    fun z ↦
      case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
        (ρ := ρ) n hS hcont hnext
        (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
        (F3 z.1) z.2 eNext
  have hraw : Continuous rawData := by
    simpa [rawData, center, ρ, κ] using
      continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
        (ρ := ρ) n hS hcont hnext
        A1passive F2 A3passive Ctop F3 eNext
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
  have htransport :
      Continuous
        (fun data :
            ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
              (K := ℝ) (ρ := ρ) κ ↦
          data.endpointTransport e) := by
    simpa [κ, κ'] using
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport
        (K := ℝ) (ρ := ρ) e
  have hYcont : Continuous Y := by
    have hretained :
        Continuous
          (fun z : η × (center → ℝ) ↦ (rawData z).endpointTransport e) :=
      htransport.comp hraw
    change Continuous
      (fun z : η × (center → ℝ) ↦ topologyTuple ((rawData z).endpointTransport e))
    exact
      (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_topologyTuple
        (K := ℝ) (ρ := ρ) (κ' := κ')).comp hretained
  have hY₀ :
      Y z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    have hdet : ((rawData z₀).endpointTransport e).detChart := by
      simpa [rawData, center, ρ, κ] using
        case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
          (ρ := ρ) n hS hcont hnext
          (A1passive z₀.1) (F2 z₀.1) (A3passive z₀.1)
          (Ctop z₀.1) (F3 z₀.1) z₀.2 eNext e
          hCtop₀ hA1passive₀
    change
      topologyTuple ((rawData z₀).endpointTransport e) ∈
        topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    simpa using
      (topologyTuple_mem_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') ((rawData z₀).endpointTransport e)).2 hdet
  simpa [Y, center, ρ, κ'] using
    exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_comp
      (M := 1) (ρ := ρ) (κ' := κ')
      (Y := Y) (a₀ := z₀) hYcont.continuousAt hY₀

set_option linter.style.longLine false in
/-- For the concrete passive product-domain measure, the retained-passive
solved-`A1` product raw-order Jacobian density is a.e. bounded above and below
by positive constants after restricting to a small open neighborhood of any
determinant-chart basepoint.

This is still only local passive chart-domain Jacobian-unit bookkeeping.  It
does not prove source-prior transport, determinant-chart Haar transport,
source-image coverage, normal crossings, pole order, or RLCT. -/
theorem exists_pos_open_ae_restrict_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type}
    [TopologicalSpace η] [MeasurableSpace η] [OpensMeasurableSpace η]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (passiveMeasure : Measure η)
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ)
    (z₀ : η × (case2ResidualBlockPivotEntries n S (J + 1) → ℝ))
    (hCtop₀ : IsUnit ((Ctop z₀.1).det))
    (hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let Y :
        η × (center → ℝ) →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦ topologyTuple (retainedData z)
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
      ∃ U : Set (η × (center → ℝ)), IsOpen U ∧ z₀ ∈ U ∧
        ∀ᵐ z ∂ sourceMeasure.restrict U,
          ε ≤
              retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z) ∧
            retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z) ≤ K := by
  intro center pivotNext signedBox weightedBox sourceMeasure retainedData Y
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  rcases
      (by
        simpa [center, retainedData, Y, ρ, κ'] using
          exists_pos_eventually_bounds_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive
            W₂ B₂ n hS hcont hnext (U₀ := U₀) eNext e
            A1passive F2 A3passive Ctop F3
            hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
            z₀ hCtop₀ hA1passive₀) with
    ⟨ε, hε_pos, K, hK_pos, hbounds⟩
  have hbounds_eventually :
      ∀ᶠ z in nhds z₀,
        ε ≤
            retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := 1) (ρ := ρ) (κ' := κ') (Y z) ∧
          retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := 1) (ρ := ρ) (κ' := κ') (Y z) ≤ K := by
    filter_upwards [hbounds.1, hbounds.2] with z hz_low hz_high
    constructor
    · simpa [Y, retainedData, center, ρ, κ'] using hz_low
    · simpa [Y, retainedData, center, ρ, κ'] using hz_high
  rcases
      exists_open_ae_restrict_of_eventually_nhds
        (μ := sourceMeasure) (x₀ := z₀) hbounds_eventually with
    ⟨U, hUopen, hz₀U, hU_bounds⟩
  exact ⟨ε, K, hε_pos, hK_pos, U, hUopen, hz₀U, hU_bounds⟩

set_option linter.style.longLine false in
/-- For the concrete passive product-domain measure, the retained-passive
solved-`A1` product raw-order Jacobian density gives a two-sided local
`withDensity` sandwich after restricting to a small open neighborhood.

This is the measure form of the local bounded-unit statement: multiplying the
passive product-domain measure by this chart-domain Jacobian factor only
changes it by bounded positive constants on the chosen local restriction.  It
does not prove source-prior transport, determinant-chart Haar transport,
source-image coverage, normal crossings, pole order, or RLCT. -/
theorem exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type}
    [TopologicalSpace η] [MeasurableSpace η] [OpensMeasurableSpace η]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (passiveMeasure : Measure η)
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ)
    (z₀ : η × (case2ResidualBlockPivotEntries n S (J + 1) → ℝ))
    (hCtop₀ : IsUnit ((Ctop z₀.1).det))
    (hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let Y :
        η × (center → ℝ) →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦ topologyTuple (retainedData z)
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
      ∃ U : Set (η × (center → ℝ)), IsOpen U ∧ z₀ ∈ U ∧
        ENNReal.ofReal ε • sourceMeasure.restrict U ≤
            (sourceMeasure.restrict U).withDensity
              (fun z ↦
                ENNReal.ofReal
                  (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                    (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                    (κ' := throughSubspaceEndpointComplementIndex
                      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))) ∧
          (sourceMeasure.restrict U).withDensity
              (fun z ↦
                ENNReal.ofReal
                  (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                    (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                    (κ' := throughSubspaceEndpointComplementIndex
                      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))) ≤
            ENNReal.ofReal K • sourceMeasure.restrict U := by
  intro center pivotNext signedBox weightedBox sourceMeasure retainedData Y
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure,
          retainedData, Y, ρ, κ'] using
          exists_pos_open_ae_restrict_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure_bounds
            W₂ B₂ n hS hcont hnext (U₀ := U₀) eNext e
            A1passive F2 A3passive Ctop F3
            hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
            passiveMeasure Rres z₀ hCtop₀ hA1passive₀) with
    ⟨ε, hε_pos, K, hK_pos, U, hUopen, hz₀U, hbounds⟩
  have hlower :
      ∀ᵐ z ∂ sourceMeasure.restrict U,
        ε ≤
          retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := ρ) (κ' := κ') (Y z) :=
    by
      simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure,
        retainedData, Y, ρ, κ'] using hbounds.1
  have hupper :
      ∀ᵐ z ∂ sourceMeasure.restrict U,
        retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := ρ) (κ' := κ') (Y z) ≤ K :=
    by
      simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure,
        retainedData, Y, ρ, κ'] using hbounds.2
  rcases
      withDensity_ofReal_sandwich_of_ae_bounds
        (μ := sourceMeasure.restrict U)
        (f := fun z ↦
          retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := ρ) (κ' := κ') (Y z))
        (ε := ε) (K := K) hlower hupper with
    ⟨hlower_measure, hupper_measure⟩
  exact ⟨ε, K, hε_pos, hK_pos, U, hUopen, hz₀U,
    hlower_measure, hupper_measure⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A passive-parameter Case 2 chart-produced source measure is supported on
the retained-passive p.13 local source when the passive chart is a.e.
measurable.

The measure on the passive domain is arbitrary.  This theorem is only support
bookkeeping for a chart pushforward; it is not a product-measure construction,
source-prior transport, Jacobian formula, normal-crossing statement, pole
order, or RLCT extraction. -/
theorem measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ] [MeasurableSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    (sourceMeasure :
      Measure
        (η ×
          ({p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ))) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily],
      AEMeasurable sourceChart sourceMeasure →
      let μ := Measure.map sourceChart sourceMeasure
      let localSource :=
        paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
          (fun E : EdgeFamily ↦ E)
      μ.restrict localSource = μ := by
  intro center EdgeFamily retainedData sourceChart _ _ hsourceChart μ localSource
  have hchart_mem :
      ∀ᵐ z ∂ sourceMeasure, sourceChart z ∈ localSource := by
    refine Filter.Eventually.of_forall ?_
    intro z
    have hpre :=
      retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3 hCtop hA1passive
    simpa [center, EdgeFamily, retainedData, sourceChart, localSource] using
      hpre.1 z
  simpa [μ, localSource] using
    measure_map_restrict_retainedPassiveP13LocalSource_eq_self_of_ae_mem
      (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EdgeFamily ↦ E)
      (η := sourceMeasure) (sourceChart := sourceChart)
      (by simpa [EdgeFamily] using (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
      hsourceChart hchart_mem

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A passive-parameter Case 2 chart-produced source measure is supported on
the named source-rank stratum when the successor rank equation holds a.e. on
the passive chart domain.

The measure on the passive domain is arbitrary, and measurability of the
passive source chart is an explicit hypothesis.  This is support bookkeeping
only; it is not source-rank coverage, source-image equality, source-prior
transport, a Jacobian formula, normal crossings, pole order, or RLCT. -/
theorem measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_sourceRankStratum_eq_self
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ] [MeasurableSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0)
    (sourceMeasure :
      Measure
        (η ×
          ({p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ))) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily],
      AEMeasurable sourceChart sourceMeasure →
      (∀ᵐ z ∂ sourceMeasure,
        r + (case2SuccessorSelectedEntryMatrix n hS hnext z.2 eNext).rank =
          rEdge 1) →
      let μ := Measure.map sourceChart sourceMeasure
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
      μ.restrict sourceStratum = μ := by
  intro center EdgeFamily retainedData sourceChart _ _ hsourceChart hr1_ae μ sourceStratum
  have hchart_mem :
      ∀ᵐ z ∂ sourceMeasure, sourceChart z ∈ sourceStratum := by
    filter_upwards [hr1_ae] with z hz
    simpa [center, EdgeFamily, retainedData, sourceChart, sourceStratum] using
      case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3 hCtop hA1passive hprod hr0 z hz
  simpa [μ, sourceStratum] using
    measure_map_restrict_sourceRankStratum_eq_self_of_ae_mem
      (W := W₂) (B := B₂)
      (Cedge := fun E : EdgeFamily ↦ E) (r := r) (rEdge := rEdge)
      (η := sourceMeasure) (sourceChart := sourceChart)
      (by simpa [EdgeFamily] using (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
      hsourceChart hchart_mem

set_option linter.style.longLine false in
/-- The passive-domain product measure with selected-entry density on the
second factor is the product base measure with the pulled-back selected-entry
density.

This is measure bookkeeping for the chart domain only.  It does not construct
a source prior, a source pushforward, a Jacobian comparison, normal crossings,
pole order, or RLCT. -/
theorem case2PassiveDomainProductMeasure_eq_prod_withDensity_sourceDensity
    {η : Type} [MeasurableSpace η] (passiveMeasure : Measure η)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let selectedDensity : (center → ℝ) → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)
    passiveMeasure.prod (signedBox.withDensity selectedDensity) =
      (passiveMeasure.prod signedBox).withDensity
        (fun z : η × (center → ℝ) ↦ selectedDensity z.2) := by
  intro center pivotNext signedBox selectedDensity
  have hdensity : AEMeasurable selectedDensity signedBox := by
    have h :=
      (SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds
        pivotNext Rres).1
    simpa [selectedDensity, signedBox] using h
  simpa [selectedDensity] using
    (prod_withDensity_right₀ (μ := passiveMeasure) (ν := signedBox) hdensity)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The concrete passive-domain product source measure is supported on the
retained-passive p.13 local source.

The source measure is `passiveMeasure.prod weightedBox`, where `weightedBox`
is the selected-entry signed box with its chart density.  Continuity of the
passive fields supplies a.e. measurability of the source chart.  This remains
chart-produced support bookkeeping only; it is not source-prior transport,
source-image equality, a Jacobian formula, normal crossings, pole order, or
RLCT. -/
theorem measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_retainedPassiveP13LocalSource_eq_self
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
    [TopologicalSpace η] [MeasurableSpace η] [OpensMeasurableSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    (passiveMeasure : Measure η)
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
      let μ := Measure.map sourceChart sourceMeasure
      let localSource :=
        paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
          (fun E : EdgeFamily ↦ E)
      μ.restrict localSource = μ := by
  intro center pivotNext signedBox weightedBox sourceMeasure EdgeFamily
    retainedData sourceChart _ _ _ μ localSource
  have hsourceChart : AEMeasurable sourceChart sourceMeasure := by
    simpa [center, EdgeFamily, retainedData, sourceChart] using
      (continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
        hCtop hA1passive).aemeasurable
  simpa [center, EdgeFamily, retainedData, sourceChart, sourceMeasure, localSource, μ] using
    (measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      A1passive F2 A3passive Ctop F3 hCtop hA1passive sourceMeasure
      hsourceChart)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The concrete passive-domain product source measure is supported on the
named source-rank stratum under the explicit Case 2 rank equations.

The successor-rank equation is uniform in the selected-entry chart coordinate
and remains an input.  This is support of the constructed chart-produced
measure only; it is not source-rank coverage, source-image equality,
source-prior transport, a Jacobian formula, normal crossings, pole order, or
RLCT. -/
theorem measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_sourceRankStratum_eq_self
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
    [TopologicalSpace η] [MeasurableSpace η] [OpensMeasurableSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0)
    (passiveMeasure : Measure η)
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
      (∀ᵐ z ∂ sourceMeasure,
        r + (case2SuccessorSelectedEntryMatrix n hS hnext z.2 eNext).rank =
          rEdge 1) →
      let μ := Measure.map sourceChart sourceMeasure
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
      μ.restrict sourceStratum = μ := by
  intro center pivotNext signedBox weightedBox sourceMeasure EdgeFamily
    retainedData sourceChart _ _ _ hr1_ae μ sourceStratum
  have hsourceChart : AEMeasurable sourceChart sourceMeasure := by
    simpa [center, EdgeFamily, retainedData, sourceChart] using
      (continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
        hCtop hA1passive).aemeasurable
  simpa [center, EdgeFamily, retainedData, sourceChart, sourceMeasure, sourceStratum, μ] using
    (measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_sourceRankStratum_eq_self
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      A1passive F2 A3passive Ctop F3 hCtop hA1passive
      hprod hr0 sourceMeasure hsourceChart hr1_ae)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The residual-coordinate marginal of the concrete passive-domain
chart-produced source measure is the selected-entry chart-image measure scaled
by the total passive mass.

The scalar `passiveMeasure Set.univ` is part of the statement because the
passive measure is arbitrary.  This is only a residual-coordinate pushforward
of a chart-produced product-domain measure; it is not determinant-chart Haar
transport, source-prior transport, a passive Jacobian formula, source-rank
coverage, normal crossings, pole order, or RLCT. -/
theorem measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_eq_smul_restrict_chartMap_image
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
    [TopologicalSpace η] [MeasurableSpace η] [OpensMeasurableSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    (passiveMeasure : Measure η)
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
      let μ := Measure.map sourceChart sourceMeasure
      let residualMap : EdgeFamily → center → ℝ :=
        fun E c ↦
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
            (residualCoordEquiv.symm c)
      Measure.map residualMap μ =
        passiveMeasure Set.univ •
          ((volume : Measure (center → ℝ)).restrict
            (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
              SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres)) := by
  intro center pivotNext signedBox weightedBox sourceMeasure EdgeFamily
    retainedData sourceChart residualCoordEquiv _ _ _ μ residualMap
  have hsourceChart : AEMeasurable sourceChart sourceMeasure := by
    simpa [center, EdgeFamily, retainedData, sourceChart] using
      (continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
        hCtop hA1passive).aemeasurable
  have hEdgeMatrix :
      Measurable (fun E : EdgeFamily ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (E p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))) := by
    simpa [EdgeFamily] using
      (paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuous
        (K := ℝ) W₂ B₂ U₀ hU₀).measurable
  have hresidualBase :
      Measurable
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)) :=
    measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
      (W := W₂) (B := B₂) U₀ hU₀ (fun E : EdgeFamily ↦ E) hEdgeMatrix
  have hresidualMap : Measurable residualMap := by
    refine measurable_pi_lambda _ ?_
    intro c
    have hc :
        Measurable (fun E : EdgeFamily ↦
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
            (residualCoordEquiv.symm c)) :=
      (measurable_pi_apply (residualCoordEquiv.symm c)).comp hresidualBase
    simpa [residualMap] using hc
  have hmap_comp :
      Measure.map residualMap μ =
        Measure.map (fun z : η × (center → ℝ) ↦ residualMap (sourceChart z))
          sourceMeasure := by
    simpa [μ, Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable
        (μ := sourceMeasure) (f := sourceChart) (g := residualMap)
        hresidualMap.aemeasurable hsourceChart)
  have hcomp :
      (fun z : η × (center → ℝ) ↦ residualMap (sourceChart z)) =ᵐ[sourceMeasure]
        fun z ↦ SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2 := by
    refine Filter.Eventually.of_forall ?_
    intro z
    funext c
    have hcoord :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3 hCtop hA1passive
        z (residualCoordEquiv.symm c)
    calc
      residualMap (sourceChart z) c =
          SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
            (residualCoordEquiv (residualCoordEquiv.symm c)) := by
        simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
          residualCoordEquiv, residualMap] using hcoord
      _ = SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2 c := by
        rw [Equiv.apply_symm_apply]
  have hmap_snd :
      Measure.map (Prod.snd : η × (center → ℝ) → center → ℝ) sourceMeasure =
        passiveMeasure Set.univ • weightedBox := by
    change
      Measure.map (Prod.snd : η × (center → ℝ) → center → ℝ)
          (passiveMeasure.prod weightedBox) =
        passiveMeasure Set.univ • weightedBox
    exact Measure.map_snd_prod (μ := passiveMeasure) (ν := weightedBox)
  have hchart_meas :
      Measurable (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext) :=
    SelectedEntrySignedBox.CenterCoord.measurable_chartMap pivotNext
  calc
    Measure.map residualMap μ =
        Measure.map (fun z : η × (center → ℝ) ↦ residualMap (sourceChart z))
          sourceMeasure := hmap_comp
    _ = Measure.map
          (fun z : η × (center → ℝ) ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2)
          sourceMeasure := Measure.map_congr hcomp
    _ = Measure.map (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
          (Measure.map (Prod.snd : η × (center → ℝ) → center → ℝ) sourceMeasure) := by
          simpa [Function.comp_def] using
            (Measure.map_map
              (μ := sourceMeasure)
              (g := SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
              (f := (Prod.snd : η × (center → ℝ) → center → ℝ))
              hchart_meas measurable_snd).symm
    _ = Measure.map (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
          (passiveMeasure Set.univ • weightedBox) := by
          rw [hmap_snd]
    _ = passiveMeasure Set.univ •
          Measure.map (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
            weightedBox := by
          exact
            Measure.map_smul (passiveMeasure Set.univ) weightedBox
              (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
    _ = passiveMeasure Set.univ •
          ((volume : Measure (center → ℝ)).restrict
            (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
              SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres)) := by
          rw [SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Finite-passive-mass residual negative-power integrability for the
passive-domain Case 2 chart-produced source measure.

The passive residual marginal is the selected-entry chart-image measure scaled
by `passiveMeasure Set.univ`, so finite total passive mass is an explicit
hypothesis.  This is a residual-coordinate marginal/integrability statement
for the chart-produced passive product measure.  It does not identify a
determinant-chart Haar measure, a raw/source Haar measure, an external source
prior, a source-image equality, a local inverse, normal crossings, pole order,
or RLCT. -/
theorem residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_finiteMass
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
    [TopologicalSpace η] [MeasurableSpace η] [OpensMeasurableSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    (passiveMeasure : Measure η)
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {t : ℝ}
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
      let μ := Measure.map sourceChart sourceMeasure
      let residualMap : EdgeFamily → center → ℝ :=
        fun E c ↦
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
            (residualCoordEquiv.symm c)
      (∀ᵐ E ∂ μ, 0 < aoyagiCoordinateSquareSum (residualMap E)) ∧
        (∫⁻ E : EdgeFamily,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualMap E)) ^ (-t))
            ∂ μ) < ∞ := by
  intro center pivotNext signedBox weightedBox sourceMeasure EdgeFamily
    retainedData sourceChart residualCoordEquiv _ _ _ μ residualMap
  have hmap :
      Measure.map residualMap μ =
        passiveMeasure Set.univ •
          ((volume : Measure (center → ℝ)).restrict
            (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
              SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres)) := by
    simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure, EdgeFamily,
      retainedData, sourceChart, residualCoordEquiv, μ, residualMap] using
      (measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_eq_smul_restrict_chartMap_image
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
        hCtop hA1passive passiveMeasure Rres)
  have htarget :
      (∀ᵐ y ∂ (volume : Measure (center → ℝ)).restrict
          (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres),
          0 < aoyagiCoordinateSquareSum y) ∧
        (∫⁻ y : center → ℝ,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum y) ^ (-t))
            ∂ (volume : Measure (center → ℝ)).restrict
                (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
                  SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres)) < ∞ := by
    simpa [center, pivotNext] using
      SelectedEntrySignedBox.CenterCoord.aoyagiCoordinateSquareSum_pos_ae_and_lintegral_rpow_neg_restrict_chartMap_image
        pivotNext ht hRres hcrit
  have hEdgeMatrix :
      Measurable (fun E : EdgeFamily ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (E p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))) := by
    simpa [EdgeFamily] using
      (paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuous
        (K := ℝ) W₂ B₂ U₀ hU₀).measurable
  have hresidualBase :
      Measurable
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)) :=
    measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
      (W := W₂) (B := B₂) U₀ hU₀ (fun E : EdgeFamily ↦ E) hEdgeMatrix
  have hresidualMap : Measurable residualMap := by
    refine measurable_pi_lambda _ ?_
    intro c
    have hc :
        Measurable (fun E : EdgeFamily ↦
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
            (residualCoordEquiv.symm c)) :=
      (measurable_pi_apply (residualCoordEquiv.symm c)).comp hresidualBase
    simpa [residualMap] using hc
  have hpos_meas :
      MeasurableSet {y : center → ℝ | 0 < aoyagiCoordinateSquareSum y} := by
    have hsquare :
        Measurable (fun y : center → ℝ ↦ aoyagiCoordinateSquareSum y) :=
      measurable_aoyagiCoordinateSquareSum measurable_id
    simpa [Set.preimage] using hsquare measurableSet_Ioi
  have hpos_map :
      ∀ᵐ y ∂ Measure.map residualMap μ, 0 < aoyagiCoordinateSquareSum y := by
    rw [hmap]
    exact Measure.ae_smul_measure htarget.1 (passiveMeasure Set.univ)
  have hpos_source :
      ∀ᵐ E ∂ μ, 0 < aoyagiCoordinateSquareSum (residualMap E) :=
    (ae_map_iff hresidualMap.aemeasurable hpos_meas).1 hpos_map
  have hpow_meas :
      Measurable (fun y : center → ℝ ↦
        ENNReal.ofReal ((aoyagiCoordinateSquareSum y) ^ (-t))) := by
    have hsquare :
        Measurable (fun y : center → ℝ ↦ aoyagiCoordinateSquareSum y) :=
      measurable_aoyagiCoordinateSquareSum measurable_id
    fun_prop
  have hfinite_map :
      (∫⁻ y : center → ℝ,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum y) ^ (-t))
          ∂ Measure.map residualMap μ) < ∞ := by
    rw [hmap, lintegral_smul_measure]
    simpa [smul_eq_mul] using
      ENNReal.mul_lt_top hpassive_lt_top htarget.2
  have hfinite_source :
      (∫⁻ E : EdgeFamily,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualMap E)) ^ (-t))
          ∂ μ) < ∞ := by
    rw [← lintegral_map hpow_meas hresidualMap]
    exact hfinite_map
  exact ⟨hpos_source, hfinite_source⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Local residual negative-power integrability after weighting the passive
domain by the retained-passive raw-order Jacobian factor.

The proof uses only domination: on a small neighborhood the Jacobian-weighted
restricted passive-domain measure is bounded above by a finite scalar multiple
of the unweighted passive product-domain measure.  After mapping by the
passive source chart, residual positivity and finite negative-power
integrability transfer from the global passive residual theorem.  This does
not identify the localized residual marginal, prove determinant-chart Haar or
source-prior transport, construct a local inverse, produce normal crossings,
pole order, or RLCT. -/
theorem exists_open_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
    [TopologicalSpace η] [MeasurableSpace η] [OpensMeasurableSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    (passiveMeasure : Measure η)
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {t : ℝ}
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (z₀ : η × (case2ResidualBlockPivotEntries n S (J + 1) → ℝ)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let Y :
        η × (center → ℝ) →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦ topologyTuple (retainedData z)
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∃ U : Set (η × (center → ℝ)), IsOpen U ∧ z₀ ∈ U ∧
      ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
        [BorelSpace EdgeFamily],
        let jacobianWeightedMeasure : Measure (η × (center → ℝ)) :=
          (sourceMeasure.restrict U).withDensity
            (fun z ↦
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                  (κ' := throughSubspaceEndpointComplementIndex
                    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)))
        let μJ := Measure.map sourceChart jacobianWeightedMeasure
        let residualMap : EdgeFamily → center → ℝ :=
          fun E c ↦
            paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
              (residualCoordEquiv.symm c)
        (∀ᵐ E ∂ μJ, 0 < aoyagiCoordinateSquareSum (residualMap E)) ∧
          (∫⁻ E : EdgeFamily,
            ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualMap E)) ^ (-t))
              ∂ μJ) < ∞ := by
  intro center pivotNext signedBox weightedBox sourceMeasure EdgeFamily
    retainedData Y sourceChart residualCoordEquiv
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure,
          retainedData, Y, ρ, κ'] using
          exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
            W₂ B₂ n hS hcont hnext (U₀ := U₀) eNext e
            A1passive F2 A3passive Ctop F3
            hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
            passiveMeasure Rres z₀ (hCtop z₀.1) (hA1passive z₀.1)) with
    ⟨ε, hε_pos, K, hK_pos, U, hUopen, hz₀U, _hlower_measure, hupper_measure⟩
  refine ⟨U, hUopen, hz₀U, ?_⟩
  intro _ _ _ jacobianWeightedMeasure μJ residualMap
  let μbase : Measure EdgeFamily := Measure.map sourceChart sourceMeasure
  have hsourceChart_meas : Measurable sourceChart := by
    simpa [center, EdgeFamily, retainedData, sourceChart] using
      (continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
        hCtop hA1passive).measurable
  have hweighted_le_restrict :
      jacobianWeightedMeasure ≤ ENNReal.ofReal K • sourceMeasure.restrict U := by
    simpa [jacobianWeightedMeasure, center, pivotNext, signedBox, weightedBox,
      sourceMeasure, retainedData, Y, ρ, κ'] using hupper_measure
  have hweighted_le_global :
      jacobianWeightedMeasure ≤ ENNReal.ofReal K • sourceMeasure :=
    measure_le_smul_of_le_smul_restrict hweighted_le_restrict
  have hμJ_le :
      μJ ≤ ENNReal.ofReal K • μbase := by
    simpa [μJ, μbase] using
      map_le_smul_map_of_le_smul hsourceChart_meas hweighted_le_global
  have hbase :
      (∀ᵐ E ∂ μbase, 0 < aoyagiCoordinateSquareSum (residualMap E)) ∧
        (∫⁻ E : EdgeFamily,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualMap E)) ^ (-t))
            ∂ μbase) < ∞ := by
    simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure, EdgeFamily,
      retainedData, sourceChart, residualCoordEquiv, μbase, residualMap] using
      (residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_finiteMass
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
        hCtop hA1passive passiveMeasure hpassive_lt_top Rres ht hRres hcrit)
  have hpos :
      ∀ᵐ E ∂ μJ, 0 < aoyagiCoordinateSquareSum (residualMap E) :=
    ae_of_measure_le_smul hμJ_le hbase.1
  have hfinite :
      (∫⁻ E : EdgeFamily,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualMap E)) ^ (-t))
          ∂ μJ) < ∞ :=
    lintegral_lt_top_of_measure_le_smul
      hμJ_le ENNReal.ofReal_lt_top hbase.2
  exact ⟨hpos, hfinite⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Residual-source packaging of the passive Jacobian-weighted Case 2 residual
integrability theorem.

The measure is still the chart-produced passive product-domain measure
restricted to the open determinant neighborhood and weighted by the formal
raw-order Jacobian factor.  This theorem only rewrites the whole-measure
residual positivity and finite lintegral as hypotheses over the retained-passive
p.13 local source; it does not identify an external source prior, prove an
exact localized residual marginal, construct normal crossings, compute pole
order, or extract RLCT. -/
theorem exists_open_residualSourceHypotheses_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
    [TopologicalSpace η] [MeasurableSpace η] [OpensMeasurableSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    (passiveMeasure : Measure η)
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {t : ℝ}
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (z₀ : η × (case2ResidualBlockPivotEntries n S (J + 1) → ℝ)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let Y :
        η × (center → ℝ) →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦ topologyTuple (retainedData z)
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    ∃ U : Set (η × (center → ℝ)), IsOpen U ∧ z₀ ∈ U ∧
      ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
        [BorelSpace EdgeFamily],
        let jacobianWeightedMeasure : Measure (η × (center → ℝ)) :=
          (sourceMeasure.restrict U).withDensity
            (fun z ↦
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                  (κ' := throughSubspaceEndpointComplementIndex
                    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)))
        let μJ := Measure.map sourceChart jacobianWeightedMeasure
        let localSource :=
          paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E)
        (∀ᵐ E ∂ μJ.restrict localSource,
            0 < aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
          residualNegPowerIntegrableOn
            (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
            (fun E : EdgeFamily ↦ E) localSource μJ t := by
  intro center pivotNext signedBox weightedBox sourceMeasure EdgeFamily
    retainedData Y sourceChart
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ≃ center :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure,
          EdgeFamily, retainedData, Y, sourceChart, residualCoordEquiv, ρ, κ'] using
          exists_open_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            A1passive F2 A3passive Ctop F3
            hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
            hCtop hA1passive passiveMeasure hpassive_lt_top
            Rres ht hRres hcrit z₀) with
    ⟨U, hUopen, hz₀U, hmain⟩
  refine ⟨U, hUopen, hz₀U, ?_⟩
  intro _ _ _ jacobianWeightedMeasure μJ localSource
  let residualMap : EdgeFamily → center → ℝ :=
    fun E c ↦
      paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
        (residualCoordEquiv.symm c)
  have hcenter :
      (∀ᵐ E ∂ μJ, 0 < aoyagiCoordinateSquareSum (residualMap E)) ∧
        (∫⁻ E : EdgeFamily,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualMap E)) ^ (-t))
            ∂ μJ) < ∞ := by
    simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure, EdgeFamily,
      retainedData, Y, sourceChart, residualCoordEquiv, jacobianWeightedMeasure,
      μJ, residualMap, ρ, κ'] using hmain
  let residualBase :
      EdgeFamily →
        AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) → ℝ :=
    fun E ↦
      paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
  have hsq : ∀ E : EdgeFamily,
      aoyagiCoordinateSquareSum (residualMap E) =
        aoyagiCoordinateSquareSum (residualBase E) := by
    intro E
    simpa [residualMap, residualBase] using
      aoyagiCoordinateSquareSum_comp_equiv residualCoordEquiv.symm (residualBase E)
  have hpos_global :
      ∀ᵐ E ∂ μJ,
        0 < aoyagiCoordinateSquareSum (residualBase E) :=
    hcenter.1.mono (fun E hE ↦ by simpa [hsq E] using hE)
  have hfinite_global :
      (∫⁻ E : EdgeFamily,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualBase E)) ^ (-t))
          ∂ μJ) < ∞ := by
    have hlintegral :
        (∫⁻ E : EdgeFamily,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualBase E)) ^ (-t))
            ∂ μJ) =
          (∫⁻ E : EdgeFamily,
            ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualMap E)) ^ (-t))
              ∂ μJ) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall (fun E ↦ by
        change
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualBase E)) ^ (-t)) =
            ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualMap E)) ^ (-t))
        rw [← hsq E])
    exact hlintegral.trans_lt hcenter.2
  have hsourceChart_meas : Measurable sourceChart := by
    simpa [center, EdgeFamily, retainedData, sourceChart] using
      (continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
        hCtop hA1passive).measurable
  have hsupport : μJ.restrict localSource = μJ := by
    simpa [center, EdgeFamily, retainedData, sourceChart, jacobianWeightedMeasure,
      μJ, localSource] using
      (measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3 hCtop hA1passive
        jacobianWeightedMeasure hsourceChart_meas.aemeasurable)
  exact ⟨by simpa [residualBase, hsupport] using hpos_global,
    by simpa [residualNegPowerIntegrableOn, residualBase, hsupport] using hfinite_global⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Passive Jacobian-weighted Case 2 local-source finite-integral handoff.

This consumes the residual-source hypotheses for the chart-produced passive
product-domain measure restricted to an open determinant neighborhood and
weighted by the formal raw-order Jacobian factor.  The local loss lower bound
and density bounds remain explicit hypotheses.  This does not identify an
external/original source prior, prove an exact localized residual marginal,
construct normal crossings, compute pole order, or extract RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
    [TopologicalSpace η] [MeasurableSpace η] [OpensMeasurableSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (passiveMeasure : Measure η)
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ)
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (z₀ : η × (case2ResidualBlockPivotEntries n S (J + 1) → ℝ)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let Y :
        η × (center → ℝ) →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦ topologyTuple (retainedData z)
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
        (fun E : EdgeFamily ↦ E)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          0 ≤ density (x, u)) →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          density (x, u) ≤ C) →
    ∃ Udom : Set (η × (center → ℝ)), IsOpen Udom ∧ z₀ ∈ Udom ∧
      ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
        [BorelSpace EdgeFamily],
        let jacobianWeightedMeasure : Measure (η × (center → ℝ)) :=
          (sourceMeasure.restrict Udom).withDensity
            (fun z ↦
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                  (κ' := throughSubspaceEndpointComplementIndex
                    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)))
        let μJ := Measure.map sourceChart jacobianWeightedMeasure
        ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
          (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
            ENNReal.ofReal
              ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                (fun u ↦
                  (loss (z.1, u)) ^
                      (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                    density (z.1, u)) z.2) ∂
          (μJ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro center pivotNext signedBox weightedBox sourceMeasure EdgeFamily
    retainedData Y sourceChart base localSource ρreg sourceStratum
    hloss hdensity_nonneg hdensity_le
  rcases
      exists_open_residualSourceHypotheses_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
        hCtop hA1passive passiveMeasure hpassive_lt_top
        Rres (le_of_lt ht) hRres hcrit z₀ with
    ⟨Udom, hUdom_open, hz₀Udom, hresidual⟩
  refine ⟨Udom, hUdom_open, hz₀Udom, ?_⟩
  intro _ _ _ jacobianWeightedMeasure μJ
  haveI : IsFiniteMeasure passiveMeasure := ⟨hpassive_lt_top⟩
  haveI : SFinite μJ := inferInstance
  have hresidual_local :
      (∀ᵐ E ∂ μJ.restrict localSource,
          0 < aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
        residualNegPowerIntegrableOn
          (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
          (fun E : EdgeFamily ↦ E) localSource μJ t := by
    simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure, EdgeFamily,
      retainedData, Y, sourceChart, jacobianWeightedMeasure, μJ, localSource] using
      hresidual
  simpa [EdgeFamily, base, localSource, ρreg, sourceStratum] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource
      (W := W₂) (B := B₂) sourceData (μ := μJ) (ν := ν)
      (loss := loss) (density := density)
      (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht
      (by
        simpa [EdgeFamily] using
          (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
      (by rfl)
      hresidual_local.1 hresidual_local.2 hloss hdensity_nonneg hdensity_le

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Passive Jacobian-weighted Case 2 finite-integral handoff with
source-stratum loss and density bounds.

This is the source-stratum-bound analogue of
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass`.
The residual positivity and residual negative-power integrability still come
from the retained-passive local source for the chart-produced passive
Jacobian-weighted measure; the regular-coordinate loss and density bounds are
only required on Aoyagi's source-rank stratum.  This does not identify an
external/original source prior, prove an exact localized residual marginal,
prove source-image equality or source-rank coverage, construct normal
crossings, compute pole order, or extract RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [Fintype τ] [DecidableEq τ]
    [TopologicalSpace η] [MeasurableSpace η] [OpensMeasurableSpace η]
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
    (A1passive :
      η → Fin 1 →
        Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix (Fin (Module.finrank ℝ U₀))
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ)
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (Ctop :
      η → Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ)
    (F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2))
        (Fin (Module.finrank ℝ U₀)) ℝ)
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3)
    (hCtop : ∀ θ : η, IsUnit ((Ctop θ).det))
    (hA1passive : ∀ θ : η, ∀ p : Fin 1, IsUnit ((A1passive θ p).det))
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (passiveMeasure : Measure η)
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ)
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (z₀ : η × (case2ResidualBlockPivotEntries n S (J + 1) → ℝ)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext).endpointTransport e
    let Y :
        η × (center → ℝ) →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦ topologyTuple (retainedData z)
    let sourceChart : η × (center → ℝ) → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData z)
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          0 ≤ density (x, u)) →
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          density (x, u) ≤ C) →
    ∃ Udom : Set (η × (center → ℝ)), IsOpen Udom ∧ z₀ ∈ Udom ∧
      ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
        [BorelSpace EdgeFamily],
        let jacobianWeightedMeasure : Measure (η × (center → ℝ)) :=
          (sourceMeasure.restrict Udom).withDensity
            (fun z ↦
              ENNReal.ofReal
                (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                  (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                  (κ' := throughSubspaceEndpointComplementIndex
                    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)))
        let μJ := Measure.map sourceChart jacobianWeightedMeasure
        ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
          (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
            ENNReal.ofReal
              ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                (fun u ↦
                  (loss (z.1, u)) ^
                      (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                    density (z.1, u)) z.2) ∂
          (μJ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro center pivotNext signedBox weightedBox sourceMeasure EdgeFamily
    retainedData Y sourceChart base ρreg sourceStratum
    hloss hdensity_nonneg hdensity_le
  let localSource :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
      (fun E : EdgeFamily ↦ E)
  rcases
      exists_open_residualSourceHypotheses_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        A1passive F2 A3passive Ctop F3
        hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
        hCtop hA1passive passiveMeasure hpassive_lt_top
        Rres (le_of_lt ht) hRres hcrit z₀ with
    ⟨Udom, hUdom_open, hz₀Udom, hresidual⟩
  refine ⟨Udom, hUdom_open, hz₀Udom, ?_⟩
  intro _ _ _ jacobianWeightedMeasure μJ
  haveI : IsFiniteMeasure passiveMeasure := ⟨hpassive_lt_top⟩
  haveI : SFinite μJ := inferInstance
  have hresidual_local :
      (∀ᵐ E ∂ μJ.restrict localSource,
          0 < aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
        residualNegPowerIntegrableOn
          (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
          (fun E : EdgeFamily ↦ E) localSource μJ t := by
    simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure, EdgeFamily,
      retainedData, Y, sourceChart, jacobianWeightedMeasure, μJ, localSource] using
      hresidual
  have hsource_meas : MeasurableSet sourceStratum := by
    dsimp [sourceStratum]
    exact
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
        (W := W₂) (B := B₂) (Cedge := fun E : EdgeFamily ↦ E)
        (r := r) (rEdge := rEdge)
        (by simpa [EdgeFamily] using
          (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
  rcases exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
      (K := ℝ) (W := W₂) (B := B₂) (x₀ := base)
      U₀ hU₀ (fun E : EdgeFamily ↦ E) r rEdge
      (by
        simpa [EdgeFamily] using
          (continuous_id : Continuous (fun E : EdgeFamily ↦ E)).continuousAt)
      (by rfl) with
    ⟨Ulocal, hUlocal_open, hbaseUlocal, _hUlocal_sub, hcoverage⟩
  simpa [EdgeFamily, base, localSource, ρreg, sourceStratum] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource
      (W := W₂) (B := B₂) sourceData
      (localSource := localSource) (μ := μJ) (ν := ν)
      (loss := loss) (density := density)
      (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht
      hsource_meas Ulocal hUlocal_open hbaseUlocal
      (by simpa [EdgeFamily, localSource, sourceStratum] using hcoverage)
      hresidual_local.1 hresidual_local.2 hloss hdensity_nonneg hdensity_le

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
/-- Endpoint-transported explicit Case 2 retained-passive data give the
fixed-base selected-entry residual coordinate readout.

This is the coordinate-level refinement of the existing residual-square-sum
corollary.  It uses the source-readback matrix handoff and does not assert any
source image, measure, Jacobian, normal-crossing, pole-order, or RLCT
consequence. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData
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
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∀ yNext c,
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
          (sourceChart yNext) c =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
          (residualCoordEquiv c) := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv
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
    paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_sourceReadback_residualFactorProduct_eq_matrix
      (M := 1) (W := W₂) (B := B₂) (pivot := pivotNext)
      (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EdgeFamily ↦ E)
      sourceChart residualCoordEquiv hpre.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 retained-passive source chart points
lie in the named source-rank stratum and p.13 local source, with residual
coordinates read back as the selected-entry chart map.

The source-rank statement is pointwise in `yNext`: the successor selected-entry
matrix rank is supplied for this chart coordinate.  This is a source-image
support/readout package only; it does not prove selected-entry source
coverage, source/image equality, source-prior transport, Jacobian
compatibility, normal crossings, pole order, or RLCT. -/
theorem case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap
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
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0) :
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
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∀ yNext : center → ℝ,
      r + (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank =
        rEdge 1 →
        sourceChart yNext ∈
          paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E)
            r rEdge ∧
        sourceChart yNext ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E) ∧
        (∀ c,
          paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
              (sourceChart yNext) c =
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
              (residualCoordEquiv c)) := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv yNext hr1
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
  have hstratum :
      sourceChart yNext ∈
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart] using
      case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        yNext hprod hr0 hr1
  refine ⟨hstratum, hpre.1 yNext, ?_⟩
  intro c
  have hcoord :=
    paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e yNext c
  simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
    residualCoordEquiv] using hcoord

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 retained-passive data give the
fixed-base residual coordinate readout after pulling back by the
nonzero-pivot selected-entry inverse.

This is a punctured-chart algebra bridge: on the locus where the selected
pivot center coordinate is nonzero, the selected-entry inverse coordinates feed
the constructed retained-passive Case 2 source chart and recover the target
center coordinates.  It does not assert source image equality, source-rank
coverage, source-prior transport, Jacobian compatibility, normal crossings,
pole order, or RLCT. -/
theorem paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
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
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∀ value : center → ℝ, value pivotNext ≠ 0 → ∀ c,
      paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
          (sourceChart
            (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
              pivotNext value)) c =
        value (residualCoordEquiv c) := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv value hpivot c
  have hcoord :=
    paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext value) c
  have hchart :=
    congrFun
      (SelectedEntrySignedBox.CenterCoord.chartMap_preimageOfPivotNeZero
        pivotNext value hpivot)
      (residualCoordEquiv c)
  simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
    residualCoordEquiv] using hcoord.trans hchart

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A nonzero selected-entry residual value produces an endpoint-transported
Case 2 retained-passive local-source point with exact residual-coordinate
readout.

This is a point-production package for the fixed-pivot punctured selected-entry
chart.  It does not assert source-rank-stratum membership, selected-entry
source-rank coverage, source-prior transport, Jacobian compatibility, normal
crossings, pole order, or RLCT. -/
theorem exists_case2EndpointTransport_sourceEdgeFamilyOfData_mem_localSource_and_residualBlockCoordinateMap_eq_value_of_pivot_ne_zero
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
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∀ value : center → ℝ, value pivotNext ≠ 0 →
      ∃ yNext : center → ℝ,
        yNext pivotNext ≠ 0 ∧
        sourceChart yNext ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E) ∧
        (∀ c,
          paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
              (sourceChart yNext) c =
            value (residualCoordEquiv c)) := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv value hpivot
  let yNext :=
    SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext value
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
  refine ⟨yNext, ?_, hpre.1 yNext, ?_⟩
  · simpa [yNext, SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero] using hpivot
  · intro c
    have hreadout :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        value hpivot c
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
      residualCoordEquiv, yNext] using hreadout

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A nonzero selected-entry residual value produces an endpoint-transported
Case 2 retained-passive point in both the source-rank stratum and the p.13
local source, with exact residual-coordinate readout.

The source-rank membership uses the explicit base-product rank, first-edge
rank, and a successor-rank hypothesis for the produced fixed-pivot inverse
coordinate.  This is still point production for one punctured selected-entry
chart value; it does not assert source-rank coverage, source/image equality,
successor-rank arithmetic, source-prior transport, Jacobian compatibility,
normal crossings, pole order, or RLCT. -/
theorem exists_case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_value_of_pivot_ne_zero
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
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0) :
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
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∀ value : center → ℝ, value pivotNext ≠ 0 →
      r +
          (case2SuccessorSelectedEntryMatrix n hS hnext
            (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
              pivotNext value)
            eNext).rank =
        rEdge 1 →
      ∃ yNext : center → ℝ,
        yNext pivotNext ≠ 0 ∧
        sourceChart yNext ∈
          paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E)
            r rEdge ∧
        sourceChart yNext ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E) ∧
        (∀ c,
          paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
              (sourceChart yNext) c =
            value (residualCoordEquiv c)) := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv value hpivot hr1
  let yNext :=
    SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext value
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
  have hyPivot : yNext pivotNext ≠ 0 := by
    simpa [yNext, SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero] using hpivot
  have hlocal :
      sourceChart yNext ∈
        paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
          (fun E : EdgeFamily ↦ E) :=
    hpre.1 yNext
  have hreadout :
      ∀ c,
        paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart yNext) c =
          value (residualCoordEquiv c) := by
    intro c
    have hcoord :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        value hpivot c
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
      residualCoordEquiv, yNext] using hcoord
  have hstratum :
      sourceChart yNext ∈
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart] using
      case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        yNext hprod hr0 (by simpa [yNext] using hr1)
  exact ⟨yNext, hyPivot, hstratum, hlocal, hreadout⟩

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
/-- The endpoint-transported Case 2 chart-produced source measure pushes
forward by the fixed-base residual-coordinate map to Lebesgue measure
restricted to the selected-entry chart image.

The measure on the source side is still the chart-produced pushforward; this
does not identify an external/original source prior, prove source-rank
coverage, compare Jacobians for an ambient prior, construct normal crossings,
compute pole order, or extract RLCT. -/
theorem measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_eq_restrict_chartMap_image
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
    {Rres :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ} :
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
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
      let sourceMeasure :=
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let μ := Measure.map sourceChart sourceMeasure
      let residualMap : EdgeFamily → center → ℝ :=
        fun E c ↦
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
            (residualCoordEquiv.symm c)
      Measure.map residualMap μ =
        (volume : Measure (center → ℝ)).restrict
          (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres) := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv _ _ _
    sourceMeasure μ residualMap
  let signedBox : Measure (center → ℝ) :=
    Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
  have hsourceChart_signed : AEMeasurable sourceChart signedBox := by
    simpa [center, EdgeFamily, retainedData, sourceChart, signedBox] using
      (continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e).aemeasurable
  have hsourceChart :
      AEMeasurable sourceChart sourceMeasure := by
    exact hsourceChart_signed.mono_ac
      (by
        simpa [sourceMeasure, signedBox] using
          withDensity_absolutelyContinuous signedBox
            (fun y : center → ℝ =>
              ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)))
  have hEdgeMatrix :
      Measurable (fun E : EdgeFamily ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (E p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))) := by
    simpa [EdgeFamily] using
      (paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuous
        (K := ℝ) W₂ B₂ U₀ hU₀).measurable
  have hresidualBase :
      Measurable
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)) :=
    measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
      (W := W₂) (B := B₂) U₀ hU₀ (fun E : EdgeFamily ↦ E) hEdgeMatrix
  have hresidualMap : Measurable residualMap := by
    refine measurable_pi_lambda _ ?_
    intro c
    have hc :
        Measurable (fun E : EdgeFamily ↦
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
            (residualCoordEquiv.symm c)) :=
      (measurable_pi_apply (residualCoordEquiv.symm c)).comp hresidualBase
    simpa [residualMap] using hc
  have hmap_comp :
      Measure.map residualMap μ =
        Measure.map (fun yNext : center → ℝ ↦ residualMap (sourceChart yNext))
          sourceMeasure := by
    simpa [μ, Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable
        (μ := sourceMeasure) (f := sourceChart) (g := residualMap)
        hresidualMap.aemeasurable hsourceChart)
  have hcomp :
      (fun yNext : center → ℝ ↦ residualMap (sourceChart yNext)) =ᵐ[sourceMeasure]
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext := by
    refine Filter.Eventually.of_forall ?_
    intro yNext
    funext c
    have hcoord :=
      paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        yNext (residualCoordEquiv.symm c)
    calc
      residualMap (sourceChart yNext) c =
          SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
            (residualCoordEquiv (residualCoordEquiv.symm c)) := by
        simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
          residualCoordEquiv, residualMap] using hcoord
      _ = SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext c := by
        rw [Equiv.apply_symm_apply]
  calc
    Measure.map residualMap μ =
        Measure.map (fun yNext : center → ℝ ↦ residualMap (sourceChart yNext))
          sourceMeasure := hmap_comp
    _ = Measure.map (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
          sourceMeasure := Measure.map_congr hcomp
    _ = (volume : Measure (center → ℝ)).restrict
          (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres) := by
          simpa [sourceMeasure] using
            SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
              pivotNext Rres

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The selected-entry chart-produced Case 2 source measure is supported on
Aoyagi's source-shaped rank stratum when the intended edge ranks hold uniformly
on the chart coordinates.

The uniform successor-rank hypothesis is explicit.  This is only support of the
constructed chart image in the source stratum; it is not source-rank coverage
or a source/image equality theorem. -/
theorem measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_restrict_sourceRankStratum_eq_self
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
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r)
    (hr0 : r + Fintype.card τ = rEdge 0)
    (hr1 :
      ∀ yNext :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ,
        r + (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank =
          rEdge 1)
    {Rres :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ} :
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
    let sourceMeasure :=
      (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
        (fun y : center → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
      let μ := Measure.map sourceChart sourceMeasure
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
      μ.restrict sourceStratum = μ := by
  intro center pivotNext EdgeFamily retainedData sourceChart sourceMeasure _ _ _ μ sourceStratum
  let signedBox : Measure (center → ℝ) :=
    Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
  have hsourceChart_signed : AEMeasurable sourceChart signedBox := by
    simpa [center, EdgeFamily, retainedData, sourceChart, signedBox] using
      (continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e).aemeasurable
  have hsourceChart :
      AEMeasurable sourceChart sourceMeasure := by
    exact hsourceChart_signed.mono_ac
      (by
        simpa [sourceMeasure, signedBox] using
          withDensity_absolutelyContinuous signedBox
            (fun y : center → ℝ =>
              ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)))
  have hchart_mem :
      ∀ᵐ yNext ∂ sourceMeasure, sourceChart yNext ∈ sourceStratum := by
    refine Filter.Eventually.of_forall ?_
    intro yNext
    simpa [center, EdgeFamily, retainedData, sourceChart, sourceStratum] using
      case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e yNext
        hprod hr0 (hr1 yNext)
  simpa [μ, sourceStratum] using
    measure_map_restrict_sourceRankStratum_eq_self_of_ae_mem
      (W := W₂) (B := B₂)
      (Cedge := fun E : EdgeFamily ↦ E) (r := r) (rEdge := rEdge)
      (η := sourceMeasure) (sourceChart := sourceChart)
      (by simpa [EdgeFamily] using (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
      hsourceChart hchart_mem

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 selected-entry data give the
determinant-chart residual hypotheses from a supplied determinant-chart
pushforward identity.

This specializes the generic selected-entry determinant-chart residual handoff.
It proves the chart a.e. measurability and residual readout from the Case 2
endpoint-transport data, but still assumes the determinant-chart pushforward
identity.  It does not identify an external/original source prior, prove chart
coverage, compare Jacobians for such a prior, construct normal crossings,
compute pole order, or extract RLCT. -/
theorem retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map
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
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    {t : ℝ} {Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ} :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := ρ) κ' :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e
    let chart : (center → ℝ) → TopologyTuple ρ κ' ℝ :=
      fun yNext ↦ topologyTuple (retainedData yNext)
    let Sdet : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let directChart : TopologyTuple ρ κ' ℝ → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W₂ B₂ U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z)
    m.restrict Sdet = Measure.map chart weightedBox →
    0 ≤ t →
    (∀ i, 0 < Rres i) →
    2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
    (∀ᵐ z ∂ m.restrict Sdet,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) (directChart z))) ∧
      (∫⁻ z : TopologyTuple ρ κ' ℝ,
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) (directChart z))) ^ (-t))
          ∂ m.restrict Sdet) < ∞ := by
  dsimp only
  intro hmap ht hRres hcrit
  let center : Finset (ℕ × ℕ) :=
    case2ResidualBlockPivotEntries n S (J + 1)
  let pivotNext : center :=
    ⟨(J + 2, J + 2),
      case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
        n hS hnext⟩
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let EdgeFamily :=
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
  let retainedData :
      (center → ℝ) →
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) κ' :=
    fun yNext ↦
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e
  let chart : (center → ℝ) → TopologyTuple ρ κ' ℝ :=
    fun yNext ↦ topologyTuple (retainedData yNext)
  let Sdet : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let signedBox : Measure (center → ℝ) :=
    Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
  let directChart : TopologyTuple ρ κ' ℝ → EdgeFamily :=
    fun z ↦
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W₂ B₂ U₀ hU₀
        (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z)
  let κ : Fin 3 → Type := case2PostPivotTwoEdgeDomain n S J τ
  have hretained_cont : Continuous retainedData := by
    have hbase :
        Continuous
          (fun yNext : center → ℝ ↦
            case2PostPivotSelectedEntryRetainedPassiveData
              (ρ := ρ) n hS hcont hnext yNext eNext) := by
      simpa [center, ρ, κ] using
        continuous_case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext eNext
    have htransport :
        Continuous
          (fun data :
              ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
                (K := ℝ) (ρ := ρ) κ ↦
            data.endpointTransport e) := by
      simpa [κ, κ'] using
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport
          (K := ℝ) (ρ := ρ) e
    simpa [retainedData, ρ, κ, κ'] using htransport.comp hbase
  have hchart_cont : Continuous chart := by
    have htop :
        Continuous
          (topologyTuple :
            ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
              (K := ℝ) (ρ := ρ) κ' →
              TopologyTuple ρ κ' ℝ) :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_topologyTuple
        (K := ℝ) (ρ := ρ) (κ' := κ')
    change Continuous (fun yNext : center → ℝ ↦ topologyTuple (retainedData yNext))
    exact htop.comp hretained_cont
  have hchart : AEMeasurable chart signedBox :=
    hchart_cont.aemeasurable
  have hsource_residual :
      ∀ yNext : center → ℝ,
        aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
              (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
                W₂ B₂ U₀ hU₀ (retainedData yNext))) =
          SelectedEntrySignedBox.CenterCoord.residual pivotNext yNext := by
    simpa [center, pivotNext, EdgeFamily, retainedData, ρ, κ'] using
      aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_case2EndpointTransport_sourceEdgeFamilyOfData
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
  have hresidual_eq :
      ∀ yNext : center → ℝ,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (directChart (chart yNext))) =
          SelectedEntrySignedBox.CenterCoord.residual pivotNext yNext := by
    intro yNext
    simpa [directChart, chart, retainedData, ρ, κ'] using hsource_residual yNext
  have hpos_meas :
      MeasurableSet {z : TopologyTuple ρ κ' ℝ |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) (directChart z))} := by
    simpa [ρ, κ', EdgeFamily, directChart] using
      measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_directChart
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
  exact
    retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_selectedEntrySignedBox_map
      (W := W₂) (B := B₂) (pivot := pivotNext)
      (U₀ := U₀) (hU₀ := hU₀) (m := m)
      (t := t) (Rres := Rres) (chart := chart)
      hchart hmap hpos_meas ht hRres hcrit hresidual_eq

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 selected-entry data give the
determinant-chart residual hypotheses for the chart-produced measure.

This is the chart-produced version of
`retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map`:
the target measure is exactly the selected-entry weighted signed-box measure
pushed forward by the endpoint-transported retained-passive determinant chart.
It proves the required determinant-chart restriction identity from pointwise
support of that chart.  It does not identify Haar measure, an external/original
source prior, full determinant-chart coverage, normal crossings, pole order, or
RLCT. -/
theorem retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_chartProducedMeasure
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
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    {t : ℝ} {Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ} :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := ρ) κ' :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e
    let chart : (center → ℝ) → TopologyTuple ρ κ' ℝ :=
      fun yNext ↦ topologyTuple (retainedData yNext)
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let targetMeasure : Measure (TopologyTuple ρ κ' ℝ) :=
      Measure.map chart weightedBox
    let directChart : TopologyTuple ρ κ' ℝ → EdgeFamily :=
      fun z ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W₂ B₂ U₀ hU₀
          (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z)
    0 ≤ t →
    (∀ i, 0 < Rres i) →
    2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
    (∀ᵐ z ∂ targetMeasure,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) (directChart z))) ∧
      (∫⁻ z : TopologyTuple ρ κ' ℝ,
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) (directChart z))) ^ (-t))
          ∂ targetMeasure) < ∞ := by
  dsimp only
  intro ht hRres hcrit
  let center : Finset (ℕ × ℕ) :=
    case2ResidualBlockPivotEntries n S (J + 1)
  let pivotNext : center :=
    ⟨(J + 2, J + 2),
      case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
        n hS hnext⟩
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let EdgeFamily :=
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
  let retainedData :
      (center → ℝ) →
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) κ' :=
    fun yNext ↦
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e
  let chart : (center → ℝ) → TopologyTuple ρ κ' ℝ :=
    fun yNext ↦ topologyTuple (retainedData yNext)
  let Sdet : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let signedBox : Measure (center → ℝ) :=
    Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
  let weightedBox : Measure (center → ℝ) :=
    signedBox.withDensity
      (fun y : center → ℝ ↦
        ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
  let κ : Fin 3 → Type := case2PostPivotTwoEdgeDomain n S J τ
  have hretained_cont : Continuous retainedData := by
    have hbase :
        Continuous
          (fun yNext : center → ℝ ↦
            case2PostPivotSelectedEntryRetainedPassiveData
              (ρ := ρ) n hS hcont hnext yNext eNext) := by
      simpa [center, ρ, κ] using
        continuous_case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext eNext
    have htransport :
        Continuous
          (fun data :
              ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
                (K := ℝ) (ρ := ρ) κ ↦
            data.endpointTransport e) := by
      simpa [κ, κ'] using
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport
          (K := ℝ) (ρ := ρ) e
    simpa [retainedData, ρ, κ, κ'] using htransport.comp hbase
  have hchart_cont : Continuous chart := by
    have htop :
        Continuous
          (topologyTuple :
            ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
              (K := ℝ) (ρ := ρ) κ' →
              TopologyTuple ρ κ' ℝ) :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_topologyTuple
        (K := ℝ) (ρ := ρ) (κ' := κ')
    change Continuous (fun yNext : center → ℝ ↦ topologyTuple (retainedData yNext))
    exact htop.comp hretained_cont
  have hchart_signed : AEMeasurable chart signedBox :=
    hchart_cont.aemeasurable
  have hSdet_meas : MeasurableSet Sdet := by
    simpa [Sdet] using
      (isOpen_topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hchart_mem : ∀ yNext : center → ℝ, chart yNext ∈ Sdet := by
    intro yNext
    have hdet :
        (retainedData yNext).detChart := by
      simpa [retainedData, ρ, κ'] using
        case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
          (ρ := ρ) n hS hcont hnext yNext eNext e
    simpa [chart, Sdet, retainedData, ρ, κ'] using
      (topologyTuple_mem_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData yNext)).2 hdet
  have hsource_residual :
      ∀ yNext : center → ℝ,
        aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
              (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
                W₂ B₂ U₀ hU₀ (retainedData yNext))) =
          SelectedEntrySignedBox.CenterCoord.residual pivotNext yNext := by
    simpa [center, pivotNext, EdgeFamily, retainedData, ρ, κ'] using
      aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_case2EndpointTransport_sourceEdgeFamilyOfData
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
  have hresidual_eq :
      ∀ yNext : center → ℝ,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
              W₂ B₂ U₀ hU₀
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') (chart yNext)))) =
          SelectedEntrySignedBox.CenterCoord.residual pivotNext yNext := by
    intro yNext
    simpa [chart, retainedData, ρ, κ'] using hsource_residual yNext
  have hpos_meas :
      MeasurableSet {z : TopologyTuple ρ κ' ℝ |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
              W₂ B₂ U₀ hU₀
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z)))} := by
    simpa [ρ, κ', EdgeFamily] using
      measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_directChart
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
  simpa [center, pivotNext, ρ, κ', EdgeFamily, retainedData, chart, signedBox,
    weightedBox] using
    retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_selectedEntrySignedBox_chartProducedMeasure
      (W := W₂) (B := B₂) (pivot := pivotNext)
      (U₀ := U₀) (hU₀ := hU₀)
      (t := t) (Rres := Rres) (chart := chart)
      hchart_signed hSdet_meas hchart_mem hpos_meas ht hRres hcrit hresidual_eq

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 selected-entry data give the
raw-order inverse-Jacobian residual-source hypotheses.

This composes the Case 2 selected-entry determinant-chart residual theorem with
the raw-order inverse-Jacobian source-measure socket.  The determinant-chart
pushforward identity remains explicit.  This does not prove chart coverage,
identify an external/original source prior, prove local loss/density bounds,
construct normal crossings, compute pole order, or extract RLCT. -/
theorem residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
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
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure] {t : ℝ}
    {Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ} :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := ρ) κ' :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e
    let chart : (center → ℝ) → TopologyTuple ρ κ' ℝ :=
      fun yNext ↦ topologyTuple (retainedData yNext)
    let Sdet : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let T : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let rawChart : TopologyTuple ρ κ' ℝ → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart (K := ℝ) W₂ B₂ U₀ hU₀
    let invJacDensity : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (topologyTupleEdgeRawOrderInverseJacobianDensity
            (ρ := ρ) (κ' := κ') y)
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
        (fun E : EdgeFamily ↦ E)
    let μ := Measure.map rawChart ((m.restrict T).withDensity invJacDensity)
    m.restrict Sdet = Measure.map chart weightedBox →
    0 ≤ t →
    (∀ i, 0 < Rres i) →
    2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
    (∀ᵐ x ∂ μ.restrict localSource,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x)) ∧
      residualNegPowerIntegrableOn
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
        (fun E : EdgeFamily ↦ E) localSource μ t := by
  dsimp only
  intro hmap ht hRres hcrit
  let center : Finset (ℕ × ℕ) :=
    case2ResidualBlockPivotEntries n S (J + 1)
  let pivotNext : center :=
    ⟨(J + 2, J + 2),
      case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
        n hS hnext⟩
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let EdgeFamily :=
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
  have hchart :
      (∀ᵐ z ∂ m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
              W₂ B₂ U₀ hU₀
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z)))) ∧
        (∫⁻ z : TopologyTuple ρ κ' ℝ,
          ENNReal.ofReal
            ((aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
                (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
                  W₂ B₂ U₀ hU₀
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z)))) ^ (-t))
            ∂ m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))) < ∞ := by
    simpa [center, pivotNext, ρ, κ', EdgeFamily] using
      retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map
        (W₂ := W₂) (B₂ := B₂) n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e (m := m) (t := t) (Rres := Rres)
        hmap ht hRres hcrit
  simpa [ρ, κ', EdgeFamily] using
    residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
      (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) (m := m) (t := t)
      hchart.1 hchart.2

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 selected-entry data give the
raw-order inverse-Jacobian finite-integral handoff.

This composes the Case 2 selected-entry determinant-chart residual theorem with
the raw-order inverse-Jacobian finite-integral socket.  The determinant-chart
pushforward identity, local loss lower bound, and local density bounds remain
explicit.  This does not prove chart coverage, identify an external/original
source prior, construct normal crossings, compute pole order, or extract RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
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
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure] [SFinite m]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    {Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := ρ) κ' :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e
    let chart : (center → ℝ) → TopologyTuple ρ κ' ℝ :=
      fun yNext ↦ topologyTuple (retainedData yNext)
    let Sdet : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let T : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let rawChart : TopologyTuple ρ κ' ℝ → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart (K := ℝ) W₂ B₂ U₀ hU₀
    let invJacDensity : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (topologyTupleEdgeRawOrderInverseJacobianDensity
            (ρ := ρ) (κ' := κ') y)
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
        (fun E : EdgeFamily ↦ E)
    let μ := Measure.map rawChart ((m.restrict T).withDensity invJacDensity)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    m.restrict Sdet = Measure.map chart weightedBox →
    (∀ i, 0 < Rres i) →
    2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          0 ≤ density (x, u)) →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          density (x, u) ≤ C) →
    ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
      (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
        ENNReal.ofReal
          ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
            (fun u ↦
              (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  dsimp only
  intro hmap hRres hcrit hloss hdensity_nonneg hdensity_le
  let center : Finset (ℕ × ℕ) :=
    case2ResidualBlockPivotEntries n S (J + 1)
  let pivotNext : center :=
    ⟨(J + 2, J + 2),
      case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
        n hS hnext⟩
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let EdgeFamily :=
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
  have hchart :
      (∀ᵐ z ∂ m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
              W₂ B₂ U₀ hU₀
              (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z)))) ∧
        (∫⁻ z : TopologyTuple ρ κ' ℝ,
          ENNReal.ofReal
            ((aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
                (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
                  W₂ B₂ U₀ hU₀
                  (ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ') z)))) ^ (-t))
            ∂ m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))) < ∞ := by
    simpa [center, pivotNext, ρ, κ', EdgeFamily] using
      retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map
        (W₂ := W₂) (B₂ := B₂) n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e (m := m) (t := t) (Rres := Rres)
        hmap (le_of_lt ht) hRres hcrit
  simpa [ρ, κ', EdgeFamily] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
      (W := W₂) (B := B₂) sourceData (m := m) (ν := ν)
      (loss := loss) (density := density) (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht hchart.1 hchart.2 hloss hdensity_nonneg hdensity_le

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 raw-order inverse-Jacobian
finite-integral handoff for a positive continuous integrand density.

This is the radius-shrinking version of
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map`:
continuity and positivity of the supplied integrand density at `(base, 0)`
produce local nonnegativity and boundedness after shrinking the
regular-coordinate radius.  The determinant-chart pushforward identity and the
local loss lower bound remain explicit.  This does not identify an
external/original source prior, prove chart coverage, construct normal
crossings, compute pole order, or extract RLCT. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map_continuousAt_pos_density
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
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure] [SFinite m]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t Rmax c : ℝ}
    {Rres : case2ResidualBlockPivotEntries n S (J + 1) → ℝ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (ht : 0 < t) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n hS hnext⟩
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let retainedData :
        (center → ℝ) →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := ρ) κ' :=
      fun yNext ↦
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e
    let chart : (center → ℝ) → TopologyTuple ρ κ' ℝ :=
      fun yNext ↦ topologyTuple (retainedData yNext)
    let Sdet : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let T : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center ↦ volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ ↦
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let rawChart : TopologyTuple ρ κ' ℝ → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart (K := ℝ) W₂ B₂ U₀ hU₀
    let invJacDensity : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (topologyTupleEdgeRawOrderInverseJacobianDensity
            (ρ := ρ) (κ' := κ') y)
    let localSource :=
      paperEndpointFixedBaseRetainedPassiveP13LocalSource W₂ B₂ U₀ hU₀
        (fun E : EdgeFamily ↦ E)
    let μ := Measure.map rawChart ((m.restrict T).withDensity invJacDensity)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    m.restrict Sdet = Measure.map chart weightedBox →
    (∀ i, 0 < Rres i) →
    2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
    ContinuousAt density (base, (0 : EuclideanSpace ℝ ρreg)) →
    0 < density (base, (0 : EuclideanSpace ℝ ρreg)) →
    (∀ᶠ x in nhdsWithin base localSource,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) Rmax →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ R C : ℝ, ∃ U : Set EdgeFamily,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ base ∈ U ∧
      (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
        ENNReal.ofReal
          ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
            (fun u ↦
              (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro center pivotNext ρ κ' EdgeFamily base retainedData chart Sdet T signedBox
    weightedBox rawChart invJacDensity localSource μ ρreg sourceStratum
    hmap hRres hcrit hdensity_cont hdensity_pos hloss
  rcases
      exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
        (α := EdgeFamily) (E := EuclideanSpace ℝ ρreg)
        (density := density) (x₀ := base) (s := localSource) (Rmax := Rmax)
        hdensity_cont hdensity_pos hRmax with
    ⟨R, C, hR, hRle, hC, hdensity_nonneg, hdensity_le⟩
  have hlossR :
      ∀ᶠ x in nhdsWithin base localSource,
        ∀ u : EuclideanSpace ℝ ρreg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u) := by
    filter_upwards [hloss] with x hx u hu
    exact hx u (Metric.ball_subset_ball hRle hu)
  rcases
      exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        sourceData (m := m) (ν := ν)
        (loss := loss) (density := density)
        (t := t) (R := R) (c := c) (C := C) (Rres := Rres)
        hR hc hC ht hmap hRres hcrit hlossR hdensity_nonneg hdensity_le with
    ⟨U, hUopen, hbaseU, hfinite⟩
  exact ⟨R, C, U, hR, hRle, hC, hUopen, hbaseU, hfinite⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 chart-produced source-stratum
two-sided handoff for a positive continuous density factor, with the residual
boundedness premise discharged by small selected-entry signed-box radii at the
produced radius.

The theorem supplies the concrete endpoint-transported Case 2 retained-passive
datum, determinant-chart proof, residual-coordinate equivalence, and
determinant-chart a.e. measurability required by the generic retained-passive
small-box theorem.  It does not choose signed-box radii or `delta`, prove
source-rank coverage or source/image equality, identify an external/original
source prior, compare Jacobians for such a prior, construct normal crossings,
compute pole order, or extract RLCT. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density_of_smallBox
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
    let DetData :=
      {data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) // data.detChart}
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily] [MeasurableSpace DetData]
      [OpensMeasurableSpace DetData] [BorelSpace DetData],
    ∀ {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ},
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀ base (fun E : EdgeFamily ↦ E) H r rEdge →
    ∀ {ν : Measure (EuclideanSpace ℝ rhoReg)} [SFinite ν],
      ν.IsAddHaarMeasure →
    ∀ {loss density : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ}
      {t Rmax cLreg CLreg : ℝ} {Rres : center → ℝ},
      0 < Rmax → 0 < cLreg → 0 < CLreg → 0 < t →
      ContinuousAt density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      0 < density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rmax →
            cLreg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rmax →
            loss (x, u) ≤ CLreg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i))) →
      let sourceMeasure :=
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let μ := Measure.map sourceChart sourceMeasure
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
      ∃ R dρ Dρ : ℝ,
        0 < R ∧ R ≤ Rmax ∧ 0 < dρ ∧ 0 ≤ Dρ ∧
        (∀ δ : ℝ,
          0 ≤ δ →
          (∀ i : center, Rres i ≤ δ) →
          δ ^ 2 * (1 + ((center.erase pivotNext.1).card : ℝ) * δ ^ 2) ≤ R ^ 2 →
          ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
            ((∫⁻ z : EdgeFamily × EuclideanSpace ℝ rhoReg,
              ENNReal.ofReal
                ((Metric.ball (0 : EuclideanSpace ℝ rhoReg) R).indicator
                  (fun u =>
                    (loss (z.1, u)) ^
                        (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                      density (z.1, u)) z.2) ∂
                (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ ↔
              residualNegPowerIntegrableOn
                (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                (fun E : EdgeFamily ↦ E) (U ∩ sourceStratum) μ t)) := by
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg DetData
    _ _ _ _ _ _ H r rEdge sourceData ν _ hν loss density t Rmax cLreg CLreg Rres
    hRmax hcLreg hCLreg ht hdensity_cont hdensity_pos hloss_lower hloss_upper
    sourceMeasure μ sourceStratum
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
  have hdet : ∀ yNext : center → ℝ, (retainedData yNext).detChart := by
    intro yNext
    simpa [retainedData] using
      case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext yNext eNext e
  have hdataFactor :
      ∀ yNext : center → ℝ,
        ChartLocalSuffixState.residualFactorProduct (retainedData yNext).C
            (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
          AoyagiResidualBlockCoordinateIndex.matrix
            (fun c ↦
              SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
                (residualCoordEquiv c)) := by
    intro yNext
    simpa [retainedData, residualCoordEquiv] using
      case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext yNext eNext e
  have hretainedData :
      AEMeasurable
        (fun yNext : center → ℝ ↦
          (⟨retainedData yNext, hdet yNext⟩ : DetData))
        (Measure.pi (fun i : center =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))) := by
    have hcontData :
        Continuous
          (fun yNext : center → ℝ ↦
            (⟨retainedData yNext, hdet yNext⟩ : DetData)) := by
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ : Fin 3 → Type := case2PostPivotTwoEdgeDomain n S J τ
      let κ' : Fin 3 → Type :=
        throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
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
        simpa [ρ, κ, κ'] using
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport_detChart_subtype
            (K := ℝ) (ρ := ρ) e
      simpa [center, retainedData, hdet, DetData, ρ, κ, κ'] using
        htransport.comp hselected
    exact hcontData.aemeasurable
  exact
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density_of_smallBox
      (M := 1) (W := W₂) (B := B₂) (pivot := pivotNext)
      (U₀ := U₀) (hU₀ := hU₀)
      (retainedData := retainedData) (hdet := hdet)
      (residualCoordEquiv := residualCoordEquiv) (hdataFactor := hdataFactor)
      (H := H) (r := r) (rEdge := rEdge)
      sourceData (ν := ν) hν
      (loss := loss) (density := density)
      (t := t) (Rmax := Rmax) (cLreg := cLreg) (CLreg := CLreg)
      (Rres := Rres)
      hretainedData hRmax hcLreg hCLreg ht hdensity_cont hdensity_pos
      hloss_lower hloss_upper

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-rank-supported version of the endpoint-transported explicit Case 2
continuous-density small-box two-sided handoff.

The explicit rank equations are used only to prove that the chart-produced
measure is supported on the source-rank stratum.  Under that support equality,
the conclusion can be stated over `μ.restrict U` and
`residualNegPowerIntegrableOn ... U μ t` rather than over
`U ∩ sourceStratum`.  This is not source-rank coverage, selected-entry
source/image equality, source-prior or Jacobian transport, normal crossings,
pole order, or RLCT. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_of_smallBox_restrict_open_of_sourceRankSupport
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
    let DetData :=
      {data :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) // data.detChart}
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily] [MeasurableSpace DetData]
      [OpensMeasurableSpace DetData] [BorelSpace DetData],
    ∀ {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ},
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀ base (fun E : EdgeFamily ↦ E) H r rEdge →
      Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r →
      r + Fintype.card τ = rEdge 0 →
      (∀ yNext : center → ℝ,
        r + (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank =
          rEdge 1) →
    ∀ {ν : Measure (EuclideanSpace ℝ rhoReg)} [SFinite ν],
      ν.IsAddHaarMeasure →
    ∀ {loss density : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ}
      {t Rmax cLreg CLreg : ℝ} {Rres : center → ℝ},
      0 < Rmax → 0 < cLreg → 0 < CLreg → 0 < t →
      ContinuousAt density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      0 < density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rmax →
            cLreg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rmax →
            loss (x, u) ≤ CLreg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i))) →
      let sourceMeasure :=
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let μ := Measure.map sourceChart sourceMeasure
      ∃ R dρ Dρ : ℝ,
        0 < R ∧ R ≤ Rmax ∧ 0 < dρ ∧ 0 ≤ Dρ ∧
        (∀ δ : ℝ,
          0 ≤ δ →
          (∀ i : center, Rres i ≤ δ) →
          δ ^ 2 * (1 + ((center.erase pivotNext.1).card : ℝ) * δ ^ 2) ≤ R ^ 2 →
          ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
            ((∫⁻ z : EdgeFamily × EuclideanSpace ℝ rhoReg,
              ENNReal.ofReal
                ((Metric.ball (0 : EuclideanSpace ℝ rhoReg) R).indicator
                  (fun u =>
                    (loss (z.1, u)) ^
                        (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                      density (z.1, u)) z.2) ∂
                (μ.restrict U).prod ν) < ∞ ↔
              residualNegPowerIntegrableOn
                (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                (fun E : EdgeFamily ↦ E) U μ t)) := by
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg DetData
    _ _ _ _ _ _ H r rEdge sourceData hprod hr0 hr1 ν _ hν
    loss density t Rmax cLreg CLreg Rres
    hRmax hcLreg hCLreg ht hdensity_cont hdensity_pos hloss_lower hloss_upper
    sourceMeasure μ
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
  rcases
      exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density_of_smallBox
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (H := H) (r := r) (rEdge := rEdge) sourceData (ν := ν) hν
        (loss := loss) (density := density)
        (t := t) (Rmax := Rmax) (cLreg := cLreg) (CLreg := CLreg)
        (Rres := Rres)
        hRmax hcLreg hCLreg ht hdensity_cont hdensity_pos
        hloss_lower hloss_upper with
    ⟨R, dρ, Dρ, hR, hRle, hdρ, hDρ, hmain⟩
  refine ⟨R, dρ, Dρ, hR, hRle, hdρ, hDρ, ?_⟩
  intro δ hδ hRres_le hsmall
  rcases hmain δ hδ hRres_le hsmall with
    ⟨U, hUopen, hbaseU, hiff⟩
  have hsupport : μ.restrict sourceStratum = μ := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
      sourceMeasure, μ, sourceStratum] using
      measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_restrict_sourceRankStratum_eq_self
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (r := r) (rEdge := rEdge) hprod hr0 hr1 (Rres := Rres)
  have hrestrict :
      μ.restrict (U ∩ sourceStratum) = μ.restrict U := by
    calc
      μ.restrict (U ∩ sourceStratum) =
          (μ.restrict sourceStratum).restrict U := by
        simpa [Set.inter_comm] using
          (Measure.restrict_restrict
            (μ := μ) (t := sourceStratum) hUopen.measurableSet).symm
      _ = μ.restrict U := by rw [hsupport]
  refine ⟨U, hUopen, hbaseU, ?_⟩
  simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
    sourceMeasure, μ, sourceStratum, residualNegPowerIntegrableOn, hrestrict] using hiff

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

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 retained-passive data give the
chart-produced selected-entry source-stratum-bound local finite-integral
handoff.

The source measure here is still the pushforward of the selected-entry
signed-box measure by the displayed endpoint-transported source chart.  The
loss and density bounds are required on the source-rank stratum.  This does not
identify an external/original source prior, prove selected-entry source/image
equality, compare Jacobians for such a prior, construct endpoint equivalences,
prove normal crossings, compute pole order, or extract RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
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
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rreg →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rreg →
            0 ≤ density (x, u)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
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
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
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
      hsourceChart hpre.1 hRres hcrit_pivot
      (aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_sourceReadback_residualFactorProduct_eq_matrix
        (W := W₂) (B := B₂) (pivot := pivotNext) sourceChart residualCoordEquiv hpre.2)
      hloss hdensity_nonneg hdensity_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- If the endpoint-transported Case 2 chart-produced measure is supported on
the source-rank stratum, the source-stratum-bound finite-integral handoff can
be stated over the open-neighborhood restriction of that same measure.

The support is supplied by explicit source-rank equations.  This does not prove
source-rank coverage, selected-entry image equality, source-prior or Jacobian
transport, normal crossings, pole order, or RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_restrict_open_of_sourceRankSupport
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
      Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r →
      r + Fintype.card τ = rEdge 0 →
      (∀ yNext : center → ℝ,
        r + (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank =
          rEdge 1) →
    ∀ {ν : Measure (EuclideanSpace ℝ rhoReg)}, ν.IsAddHaarMeasure →
    ∀ {loss density : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ}
      {t Rreg creg Creg : ℝ} {Rres : center → ℝ},
      0 < Rreg → 0 < creg → 0 ≤ Creg → 0 < t →
      (∀ i, 0 < Rres i) →
      2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rreg →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rreg →
            0 ≤ density (x, u)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rreg →
            density (x, u) ≤ Creg) →
      let sourceMeasure :=
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let μ := Measure.map sourceChart sourceMeasure
      ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
        (∫⁻ z : EdgeFamily × EuclideanSpace ℝ rhoReg,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ rhoReg) Rreg).indicator
              (fun u =>
                (loss (z.1, u)) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict U).prod ν) < ∞ := by
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg _ _ _
    H r rEdge sourceData hprod hr0 hr1 ν hν loss density t Rreg creg Creg Rres
    hRreg hcreg hCreg ht hRres hcrit_pivot hloss hdensity_nonneg hdensity_le
    sourceMeasure μ
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
  rcases
      exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (H := H) (r := r) (rEdge := rEdge) sourceData (ν := ν) hν
        (loss := loss) (density := density)
        (t := t) (Rreg := Rreg) (creg := creg) (Creg := Creg) (Rres := Rres)
        hRreg hcreg hCreg ht hRres hcrit_pivot
        hloss hdensity_nonneg hdensity_le with
    ⟨U, hUopen, hbaseU, hfinite⟩
  have hsupport : μ.restrict sourceStratum = μ := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
      sourceMeasure, μ, sourceStratum] using
      measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_restrict_sourceRankStratum_eq_self
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (r := r) (rEdge := rEdge) hprod hr0 hr1 (Rres := Rres)
  have hrestrict :
      μ.restrict (U ∩ sourceStratum) = μ.restrict U := by
    calc
      μ.restrict (U ∩ sourceStratum) =
          (μ.restrict sourceStratum).restrict U := by
        simpa [Set.inter_comm] using
          (Measure.restrict_restrict
            (μ := μ) (t := sourceStratum) hUopen.measurableSet).symm
      _ = μ.restrict U := by rw [hsupport]
  refine ⟨U, hUopen, hbaseU, ?_⟩
  rw [← hrestrict]
  simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
    sourceMeasure, μ, sourceStratum] using hfinite

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 chart-produced source-stratum-bound
finite-integral handoff for a positive continuous density factor.

Continuity and positivity of the transported density at `(base,0)` produce
source-stratum density bounds after shrinking the regular-coordinate radius.
The source measure remains the selected-entry chart-produced pushforward. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
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
      {t Rmax creg : ℝ} {Rres : center → ℝ},
      0 < Rmax → 0 < creg → 0 < t →
      (∀ i, 0 < Rres i) →
      2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
      ContinuousAt density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      0 < density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      (∀ᶠ x in nhdsWithin base
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge),
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
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg
    _ _ _ H r rEdge sourceData ν hν loss density t Rmax creg Rres
    hRmax hcreg ht hRres hcrit_pivot hdensity_cont hdensity_pos hloss
    sourceMeasure μ sourceStratum
  rcases
      exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
        (α := EdgeFamily) (E := EuclideanSpace ℝ rhoReg)
        (density := density) (x₀ := base) (s := sourceStratum) (Rmax := Rmax)
        hdensity_cont hdensity_pos hRmax with
    ⟨R, C, hR, hRle, hC, hdensity_nonneg, hdensity_le⟩
  have hlossR :
      ∀ᶠ x in nhdsWithin base sourceStratum,
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) R →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u) := by
    filter_upwards [hloss] with x hx u hu
    exact hx u (Metric.ball_subset_ball hRle hu)
  rcases
      exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (H := H) (r := r) (rEdge := rEdge) sourceData (ν := ν) hν
        (loss := loss) (density := density)
        (t := t) (Rreg := R) (creg := creg) (Creg := C) (Rres := Rres)
        hR hcreg hC ht hRres hcrit_pivot hlossR hdensity_nonneg hdensity_le with
    ⟨U, hUopen, hbaseU, hfinite⟩
  exact ⟨R, C, U, hR, hRle, hC, hUopen, hbaseU, hfinite⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 chart-produced finite-integral
handoff for Aoyagi's adapted p.13 product-difference square-sum.

The regular-plus-residual lower bound is derived from the source-side
product-coordinate theorem for the self-base multi-edge product family; it is
not an external loss-comparison hypothesis.  The source measure remains the
selected-entry chart-produced pushforward. -/
theorem exists_radius_open_lintegral_ofReal_adaptedProductDifferenceSquareSum_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
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
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
    ∀ {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ},
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀ base (fun E : EdgeFamily ↦ E) H r rEdge →
    ∀ {ν : Measure (EuclideanSpace ℝ rhoReg)}, ν.IsAddHaarMeasure →
    ∀ {density : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ}
      {t Rmax : ℝ} {Rres : center → ℝ},
      0 < Rmax → 0 < t →
      (∀ i, 0 < Rres i) →
      2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
      ContinuousAt density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      0 < density (base, (0 : EuclideanSpace ℝ rhoReg)) →
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
                (paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                    (K := ℝ) W₂ B₂ U₀ hU₀ CedgeProd (z.1, u)) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg CedgeProd
    _ _ _ H r rEdge sourceData ν hν density t Rmax Rres
    hRmax ht hRres hcrit_pivot hdensity_cont hdensity_pos
    sourceMeasure μ sourceStratum
  rcases
      exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
        (α := EdgeFamily) (E := EuclideanSpace ℝ rhoReg)
        (density := density) (x₀ := base) (s := sourceStratum) (Rmax := Rmax)
        hdensity_cont hdensity_pos hRmax with
    ⟨Rden, C, hRden, hRden_le, hC, hdensity_nonneg_den, hdensity_le_den⟩
  rcases
      exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
        (V := W₂) (Bv := B₂) (x₀ := base) U₀ hU₀
        (fun E : EdgeFamily ↦ E)
        (by
          simpa [EdgeFamily] using
            (continuous_id : Continuous (fun E : EdgeFamily ↦ E)).continuousAt)
        (by rfl)
        (r := r) (rEdge := rEdge) (Rmax := Rden) hRden with
    ⟨R, creg, hR, hR_le_Rden, hcreg, hadapted_lower⟩
  have hdensity_nonneg :
      ∀ᶠ x in nhdsWithin base sourceStratum,
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) R →
            0 ≤ density (x, u) := by
    filter_upwards [hdensity_nonneg_den] with x hx u hu
    exact hx u (Metric.ball_subset_ball hR_le_Rden hu)
  have hdensity_le :
      ∀ᶠ x in nhdsWithin base sourceStratum,
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) R →
            density (x, u) ≤ C := by
    filter_upwards [hdensity_le_den] with x hx u hu
    exact hx u (Metric.ball_subset_ball hR_le_Rden hu)
  have hloss :
      ∀ᶠ x in nhdsWithin base sourceStratum,
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) R →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W₂ B₂ U₀ hU₀ CedgeProd (x, u) := by
    simpa [rhoReg, CedgeProd, sourceStratum] using hadapted_lower
  rcases
      exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (H := H) (r := r) (rEdge := rEdge) sourceData (ν := ν) hν
        (loss := fun z : EdgeFamily × EuclideanSpace ℝ rhoReg ↦
          paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
            (K := ℝ) W₂ B₂ U₀ hU₀ CedgeProd z)
        (density := density)
        (t := t) (Rreg := R) (creg := creg) (Creg := C) (Rres := Rres)
        hR hcreg hC ht hRres hcrit_pivot
        hloss hdensity_nonneg hdensity_le with
    ⟨U, hUopen, hbaseU, hfinite⟩
  refine ⟨R, C, U, hR, hR_le_Rden.trans hRden_le, hC, hUopen, hbaseU, ?_⟩
  simpa [rhoReg, CedgeProd, sourceMeasure, μ, sourceStratum] using hfinite

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 chart-produced finite-integral
handoff for original endpoint square-Frobenius `lossDLN` in supplied endpoint
bases.

The lower bound is obtained by composing the source-side adapted p.13
product-difference lower bound with the finite endpoint-basis comparison from
adapted Frobenius loss to `lossDLN`.  The source measure remains the
selected-entry chart-produced pushforward; no external source-prior or
Jacobian transport is asserted. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
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
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
    ∀ {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ},
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀ base (fun E : EdgeFamily ↦ E) H r rEdge →
    ∀ {d : Fin 3 → ℕ},
      (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j)) →
    ∀ {ν : Measure (EuclideanSpace ℝ rhoReg)}, ν.IsAddHaarMeasure →
    ∀ {density : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ}
      {t Rmax : ℝ} {Rres : center → ℝ},
      0 < Rmax → 0 < t →
      (∀ i, 0 < Rres i) →
      2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
      ContinuousAt density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      0 < density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      let sourceMeasure :=
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let μ := Measure.map sourceChart sourceMeasure
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
      let target :=
        LinearMap.toMatrix (b 0) (b (Fin.last 2))
          (chainMap (reverseVertex W₂) (reverseEdge W₂ B₂)
            0 (Fin.last 2) (Fin.zero_le (Fin.last 2)))
      ∃ R C : ℝ, ∃ U : Set EdgeFamily,
        0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ base ∈ U ∧
        (∫⁻ z : EdgeFamily × EuclideanSpace ℝ rhoReg,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ rhoReg) R).indicator
              (fun u =>
                (lossDLN d target
                    (chainMapMatrixTuple b
                      (fun p : Fin 2 =>
                        (CedgeProd (z.1, u) p :
                          reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg CedgeProd
    _ _ _ H r rEdge sourceData d b ν hν density t Rmax Rres
    hRmax ht hRres hcrit_pivot hdensity_cont hdensity_pos
    sourceMeasure μ sourceStratum target
  classical
  let target' : Matrix (Fin (d (Fin.last 2))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last 2))
      (chainMap (reverseVertex W₂) (reverseEdge W₂ B₂)
        0 (Fin.last 2) (Fin.zero_le (Fin.last 2)))
  let originalLoss : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ :=
    fun z ↦
      lossDLN d target'
        (chainMapMatrixTuple b
          (fun p : Fin 2 =>
            (CedgeProd z p :
              reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)))
  rcases
      exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
        (W := W₂) (B := B₂) b U₀ hU₀ CedgeProd with
    ⟨c0, hc0, hcmp⟩
  rcases
      exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
        (α := EdgeFamily) (E := EuclideanSpace ℝ rhoReg)
        (density := density) (x₀ := base) (s := sourceStratum) (Rmax := Rmax)
        hdensity_cont hdensity_pos hRmax with
    ⟨Rden, C, hRden, hRden_le, hC, hdensity_nonneg_den, hdensity_le_den⟩
  rcases
      exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
        (V := W₂) (Bv := B₂) (x₀ := base) U₀ hU₀
        (fun E : EdgeFamily ↦ E)
        (by
          simpa [EdgeFamily] using
            (continuous_id : Continuous (fun E : EdgeFamily ↦ E)).continuousAt)
        (by rfl)
        (r := r) (rEdge := rEdge) (Rmax := Rden) hRden with
    ⟨R, cprod, hR, hR_le_Rden, hcprod, hadapted_lower⟩
  have hdensity_nonneg :
      ∀ᶠ x in nhdsWithin base sourceStratum,
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) R →
            0 ≤ density (x, u) := by
    filter_upwards [hdensity_nonneg_den] with x hx u hu
    exact hx u (Metric.ball_subset_ball hR_le_Rden hu)
  have hdensity_le :
      ∀ᶠ x in nhdsWithin base sourceStratum,
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) R →
            density (x, u) ≤ C := by
    filter_upwards [hdensity_le_den] with x hx u hu
    exact hx u (Metric.ball_subset_ball hR_le_Rden hu)
  have hloss :
      ∀ᶠ x in nhdsWithin base sourceStratum,
        ∀ u : EuclideanSpace ℝ rhoReg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ rhoReg) R →
            (c0 * cprod) * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ originalLoss (x, u) := by
    filter_upwards [hadapted_lower] with x hx
    intro u hu
    have hsq :
        c0 * paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
            (K := ℝ) W₂ B₂ U₀ hU₀ CedgeProd (x, u) ≤
          originalLoss (x, u) := by
      have hcmp' := hcmp (x, u)
      rw [paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
        (W := W₂) (B := B₂) U₀ hU₀ CedgeProd (x, u)] at hcmp'
      simpa [originalLoss, target'] using hcmp'
    calc
      (c0 * cprod) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i => u i))
          = c0 * (cprod *
              (aoyagiCoordinateSquareSum
                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                    (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
                aoyagiCoordinateSquareSum (fun i => u i))) := by ring
      _ ≤ c0 * paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
            (K := ℝ) W₂ B₂ U₀ hU₀ CedgeProd (x, u) :=
          mul_le_mul_of_nonneg_left
            (by simpa [rhoReg, CedgeProd, sourceStratum] using hx u hu)
            (le_of_lt hc0)
      _ ≤ originalLoss (x, u) := hsq
  rcases
      exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (H := H) (r := r) (rEdge := rEdge) sourceData (ν := ν) hν
        (loss := originalLoss)
        (density := density)
        (t := t) (Rreg := R) (creg := c0 * cprod) (Creg := C) (Rres := Rres)
        hR (mul_pos hc0 hcprod) hC ht hRres hcrit_pivot
        hloss hdensity_nonneg hdensity_le with
    ⟨U, hUopen, hbaseU, hfinite⟩
  refine ⟨R, C, U, hR, hR_le_Rden.trans hRden_le, hC, hUopen, hbaseU, ?_⟩
  simpa [rhoReg, CedgeProd, target, target', originalLoss, sourceMeasure, μ, sourceStratum] using hfinite

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-transported explicit Case 2 chart-produced finite-integral
handoff for original endpoint square-Frobenius `lossDLN`, with the concrete
p.13 product-step inverse-Jacobian density.

This is the concrete-density specialization of
`exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density`.
The continuity and positivity of the density are discharged by the p.13
raw-order tuple density lemmas. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
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
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
    ∀ {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ},
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀ base (fun E : EdgeFamily ↦ E) H r rEdge →
    ∀ {d : Fin 3 → ℕ},
      (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j)) →
    ∀ {ν : Measure (EuclideanSpace ℝ rhoReg)}, ν.IsAddHaarMeasure →
    ∀ {t Rmax : ℝ} {Rres : center → ℝ},
      0 < Rmax → 0 < t →
      (∀ i, 0 < Rres i) →
      2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
      let invJacDensity : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ :=
        fun xu ↦
          productReductionStepRawOrderInverseJacobianDensity
            (paperEndpointFixedBaseP13RawOrderTuple
              W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) xu)
      let sourceMeasure :=
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let μ := Measure.map sourceChart sourceMeasure
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
      let target :=
        LinearMap.toMatrix (b 0) (b (Fin.last 2))
          (chainMap (reverseVertex W₂) (reverseEdge W₂ B₂)
            0 (Fin.last 2) (Fin.zero_le (Fin.last 2)))
      ∃ R C : ℝ, ∃ U : Set EdgeFamily,
        0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ base ∈ U ∧
        (∫⁻ z : EdgeFamily × EuclideanSpace ℝ rhoReg,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ rhoReg) R).indicator
              (fun u =>
                (lossDLN d target
                    (chainMapMatrixTuple b
                      (fun p : Fin 2 =>
                        (CedgeProd (z.1, u) p :
                          reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                  invJacDensity (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg CedgeProd
    _ _ _ H r rEdge sourceData d b ν hν t Rmax Rres
    hRmax ht hRres hcrit_pivot invJacDensity sourceMeasure μ sourceStratum target
  classical
  have hCedgeBase :
      ContinuousAt (fun E : EdgeFamily ↦ E) base := by
    simpa using (continuous_id : Continuous (fun E : EdgeFamily ↦ E)).continuousAt
  have hbase :
      (fun E : EdgeFamily ↦ E) base =
        fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p) := by
    rfl
  have hdensity_cont :
      ContinuousAt invJacDensity (base, (0 : EuclideanSpace ℝ rhoReg)) := by
    simpa [invJacDensity, rhoReg] using
      continuousAt_paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_selfBase
        (M := 0) (V := W₂) (Bv := B₂) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := fun E : EdgeFamily ↦ E) hCedgeBase hbase
  have hdensity_pos :
      0 < invJacDensity (base, (0 : EuclideanSpace ℝ rhoReg)) := by
    simpa [invJacDensity, rhoReg] using
      paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center
        (M := 0) (V := W₂) (Bv := B₂) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := fun E : EdgeFamily ↦ E) base
  simpa [invJacDensity, sourceMeasure, μ, sourceStratum, target] using
    exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      (H := H) (r := r) (rEdge := rEdge) sourceData b (ν := ν) hν
      (density := invJacDensity)
      (t := t) (Rmax := Rmax) (Rres := Rres)
      hRmax ht hRres hcrit_pivot hdensity_cont hdensity_pos

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-rank-supported version of the endpoint-transported explicit Case 2
chart-produced finite-integral handoff for original endpoint square-Frobenius
`lossDLN` in supplied endpoint bases.

The explicit rank equations are used only to prove support of the
chart-produced measure on the source-rank stratum, allowing the final
restriction to be stated as `μ.restrict U`.  This is not source-rank coverage,
selected-entry source/image equality, source-prior transport, Jacobian
transport, normal crossings, pole order, or RLCT. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_restrict_open_of_sourceRankSupport
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
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
    ∀ {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ},
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀ base (fun E : EdgeFamily ↦ E) H r rEdge →
      Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r →
      r + Fintype.card τ = rEdge 0 →
      (∀ yNext : center → ℝ,
        r + (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank =
          rEdge 1) →
    ∀ {d : Fin 3 → ℕ},
      (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j)) →
    ∀ {ν : Measure (EuclideanSpace ℝ rhoReg)}, ν.IsAddHaarMeasure →
    ∀ {density : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ}
      {t Rmax : ℝ} {Rres : center → ℝ},
      0 < Rmax → 0 < t →
      (∀ i, 0 < Rres i) →
      2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
      ContinuousAt density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      0 < density (base, (0 : EuclideanSpace ℝ rhoReg)) →
      let sourceMeasure :=
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let μ := Measure.map sourceChart sourceMeasure
      let target :=
        LinearMap.toMatrix (b 0) (b (Fin.last 2))
          (chainMap (reverseVertex W₂) (reverseEdge W₂ B₂)
            0 (Fin.last 2) (Fin.zero_le (Fin.last 2)))
      ∃ R C : ℝ, ∃ U : Set EdgeFamily,
        0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ base ∈ U ∧
        (∫⁻ z : EdgeFamily × EuclideanSpace ℝ rhoReg,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ rhoReg) R).indicator
              (fun u =>
                (lossDLN d target
                    (chainMapMatrixTuple b
                      (fun p : Fin 2 =>
                        (CedgeProd (z.1, u) p :
                          reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict U).prod ν) < ∞ := by
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg CedgeProd
    _ _ _ H r rEdge sourceData hprod hr0 hr1 d b ν hν density t Rmax Rres
    hRmax ht hRres hcrit_pivot hdensity_cont hdensity_pos
    sourceMeasure μ target
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
  rcases
      exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (H := H) (r := r) (rEdge := rEdge) sourceData b (ν := ν) hν
        (density := density)
        (t := t) (Rmax := Rmax) (Rres := Rres)
        hRmax ht hRres hcrit_pivot hdensity_cont hdensity_pos with
    ⟨R, C, U, hR, hRle, hC, hUopen, hbaseU, hfinite⟩
  have hsupport : μ.restrict sourceStratum = μ := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
      sourceMeasure, μ, sourceStratum] using
      measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_restrict_sourceRankStratum_eq_self
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (r := r) (rEdge := rEdge) hprod hr0 hr1 (Rres := Rres)
  have hrestrict :
      μ.restrict (U ∩ sourceStratum) = μ.restrict U := by
    calc
      μ.restrict (U ∩ sourceStratum) =
          (μ.restrict sourceStratum).restrict U := by
        simpa [Set.inter_comm] using
          (Measure.restrict_restrict
            (μ := μ) (t := sourceStratum) hUopen.measurableSet).symm
      _ = μ.restrict U := by rw [hsupport]
  refine ⟨R, C, U, hR, hRle, hC, hUopen, hbaseU, ?_⟩
  rw [← hrestrict]
  simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
    rhoReg, CedgeProd, sourceMeasure, μ, sourceStratum, target] using hfinite

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-rank-supported version of the endpoint-transported explicit Case 2
finite-integral handoff for endpoint `lossDLN`, with the concrete p.13
product-step inverse-Jacobian density.

The explicit rank equations are used only to prove that the chart-produced
measure is supported on the source-rank stratum, so the final restriction can
be stated as `μ.restrict U`. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_restrict_open_of_sourceRankSupport
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
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
      [BorelSpace EdgeFamily],
    ∀ {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ},
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀ base (fun E : EdgeFamily ↦ E) H r rEdge →
      Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r →
      r + Fintype.card τ = rEdge 0 →
      (∀ yNext : center → ℝ,
        r + (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank =
          rEdge 1) →
    ∀ {d : Fin 3 → ℕ},
      (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j)) →
    ∀ {ν : Measure (EuclideanSpace ℝ rhoReg)}, ν.IsAddHaarMeasure →
    ∀ {t Rmax : ℝ} {Rres : center → ℝ},
      0 < Rmax → 0 < t →
      (∀ i, 0 < Rres i) →
      2 * t < ((center.erase pivotNext.1).card : ℝ) + 1 →
      let invJacDensity : EdgeFamily × EuclideanSpace ℝ rhoReg → ℝ :=
        fun xu ↦
          productReductionStepRawOrderInverseJacobianDensity
            (paperEndpointFixedBaseP13RawOrderTuple
              W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) xu)
      let sourceMeasure :=
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
          (fun y : center → ℝ =>
            ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let μ := Measure.map sourceChart sourceMeasure
      let target :=
        LinearMap.toMatrix (b 0) (b (Fin.last 2))
          (chainMap (reverseVertex W₂) (reverseEdge W₂ B₂)
            0 (Fin.last 2) (Fin.zero_le (Fin.last 2)))
      ∃ R C : ℝ, ∃ U : Set EdgeFamily,
        0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ base ∈ U ∧
        (∫⁻ z : EdgeFamily × EuclideanSpace ℝ rhoReg,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ rhoReg) R).indicator
              (fun u =>
                (lossDLN d target
                    (chainMapMatrixTuple b
                      (fun p : Fin 2 =>
                        (CedgeProd (z.1, u) p :
                          reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                  invJacDensity (z.1, u)) z.2) ∂
            (μ.restrict U).prod ν) < ∞ := by
  intro center pivotNext EdgeFamily base retainedData sourceChart rhoReg CedgeProd
    _ _ _ H r rEdge sourceData hprod hr0 hr1 d b ν hν t Rmax Rres
    hRmax ht hRres hcrit_pivot invJacDensity sourceMeasure μ target
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
  rcases
      exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (H := H) (r := r) (rEdge := rEdge) sourceData b (ν := ν) hν
        (t := t) (Rmax := Rmax) (Rres := Rres)
        hRmax ht hRres hcrit_pivot with
    ⟨R, C, U, hR, hRle, hC, hUopen, hbaseU, hfinite⟩
  have hsupport : μ.restrict sourceStratum = μ := by
    simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
      sourceMeasure, μ, sourceStratum] using
      measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_restrict_sourceRankStratum_eq_self
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        (r := r) (rEdge := rEdge) hprod hr0 hr1 (Rres := Rres)
  have hrestrict :
      μ.restrict (U ∩ sourceStratum) = μ.restrict U := by
    calc
      μ.restrict (U ∩ sourceStratum) =
          (μ.restrict sourceStratum).restrict U := by
        simpa [Set.inter_comm] using
          (Measure.restrict_restrict
            (μ := μ) (t := sourceStratum) hUopen.measurableSet).symm
      _ = μ.restrict U := by rw [hsupport]
  refine ⟨R, C, U, hR, hRle, hC, hUopen, hbaseU, ?_⟩
  rw [← hrestrict]
  simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
    rhoReg, CedgeProd, invJacDensity, sourceMeasure, μ, sourceStratum, target] using hfinite

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Endpoint-cardinality version of the endpoint-transported explicit Case 2
chart-produced finite-integral handoff for a positive continuous density
factor.

The endpoint equivalences are constructed noncanonically from the supplied
finite cardinality equalities by `case2EndpointTransportEquivs_of_card_eq`.
This does not prove the cardinality equalities, preserve labels, identify an
external/original source prior, compare Jacobians for such a prior, construct
normal crossings, compute pole order, or extract RLCT. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_card_eq
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
    let equivs :=
      case2EndpointTransportEquivs_of_card_eq
        (κ := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
        n S J hNext hEndpoints
    let eNext := equivs.1
    let e := equivs.2
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
  intro center pivotNext equivs eNext e EdgeFamily base retainedData sourceChart
    rhoReg localSource _ _ _ H r rEdge sourceData ν hν loss density t Rmax creg
    Rres hRmax hcreg ht hRres hcrit_pivot hdensity_cont hdensity_pos hloss
    sourceMeasure μ sourceStratum
  simpa [center, pivotNext, equivs, eNext, e, EdgeFamily, base, retainedData,
    sourceChart, rhoReg, localSource, sourceMeasure, μ, sourceStratum] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) equivs.1 equivs.2
      (H := H) (r := r) (rEdge := rEdge) sourceData (ν := ν) hν
      (loss := loss) (density := density)
      (t := t) (Rmax := Rmax) (creg := creg) (Rres := Rres)
      hRmax hcreg ht hRres hcrit_pivot hdensity_cont hdensity_pos hloss

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
