import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource

/-!
# Retained-passive Case 2 passive selected-entry source chart

This file packages the passive-parameter selected-entry retained-passive datum
as a local fixed-base p.13 source chart.  It proves an open determinant-domain
source/readback theorem for the full retained-passive coordinates.  It does
not prove source-image coverage, source-prior transport, determinant-chart
Haar transport, a Jacobian theorem, normal crossings, pole order, or RLCT.
-/

noncomputable section

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
/-- Near a base passive selected-entry point whose retained determinant
coordinates are units, the endpoint-transported passive selected-entry source
chart lies in the retained-passive p.13 local source and source readback
recovers the full transported retained-passive datum.

This is a local source-coordinate inverse/readback theorem.  It is not
source-image equality, source-rank coverage, determinant-chart Haar transport,
source-prior transport, a Jacobian comparison, normal crossings, pole order,
or RLCT extraction. -/
theorem exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [TopologicalSpace η] [Fintype τ] [DecidableEq τ]
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
    (z₀ : η × (case2ResidualBlockPivotEntries n S (J + 1) → ℝ))
    (hCtop₀ : IsUnit ((Ctop z₀.1).det))
    (hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        η × (center → ℝ) →
          RetainedPassiveNonredundantCoordinateData
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
    ∃ U : Set (η × (center → ℝ)),
      IsOpen U ∧ z₀ ∈ U ∧
        ∀ z ∈ U,
          sourceChart z ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
            (let E :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p : Fin 2 ↦
                  (sourceChart z p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
              retainedData z) := by
  intro center EdgeFamily retainedData sourceChart
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ : Fin 3 → Type := case2PostPivotTwoEdgeDomain n S J τ
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let rawData :
      η × (center → ℝ) →
        RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ :=
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
            RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ ↦
          data.endpointTransport e) := by
    simpa [κ, κ'] using
      continuous_endpointTransport (K := ℝ) (ρ := ρ) e
  have hretained : Continuous retainedData := by
    change Continuous
      (fun z : η × (center → ℝ) ↦ (rawData z).endpointTransport e)
    exact htransport.comp hraw
  let Y :
      η × (center → ℝ) → TopologyTuple ρ κ' ℝ :=
    fun z ↦ topologyTuple (retainedData z)
  have hYcont : Continuous Y := by
    exact (continuous_topologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')).comp hretained
  have hY₀ : Y z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    have hdet : (retainedData z₀).detChart := by
      simpa [retainedData, rawData, center, ρ, κ, κ'] using
        case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
          (ρ := ρ) n hS hcont hnext
          (A1passive z₀.1) (F2 z₀.1) (A3passive z₀.1)
          (Ctop z₀.1) (F3 z₀.1) z₀.2 eNext e
          hCtop₀ hA1passive₀
    simpa [Y] using
      (topologyTuple_mem_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z₀)).2 hdet
  let detSet : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let U : Set (η × (center → ℝ)) := Y ⁻¹' detSet
  refine ⟨U, ?_, ?_, ?_⟩
  · exact
      hYcont.isOpen_preimage detSet
        (by
          simpa [detSet, ρ, κ'] using
            (isOpen_topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')))
  · simpa [U, detSet] using hY₀
  · intro z hz
    have hYz : Y z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
      simpa [U, detSet] using hz
    have hdet : (retainedData z).detChart := by
      exact
        (topologyTuple_mem_topologyTupleDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z)).1
          (by simpa [Y] using hYz)
    constructor
    · dsimp [paperEndpointFixedBaseRetainedPassiveP13LocalSource]
      rw [
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
          (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) (retainedData z)]
      exact
        sourceRecursiveDetChart_edgeMatrix_of_detChart
          (K := ℝ) (ρ := ρ) (retainedData z) hdet
    · let E :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (sourceChart z p :
              reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
      have hedge :
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
              (fun p : Fin 2 ↦
                ((fun E : EdgeFamily ↦ E) (sourceChart z) p :
                  reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)) =
            (retainedData z).edgeMatrix := by
        simpa [sourceChart] using
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
            (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) (retainedData z)
      simpa [E] using
        sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq
          (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
          (Cedge := fun E : EdgeFamily ↦ E)
          (sourceChart z) (retainedData z) hdet hedge

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- On the open determinant-domain from the passive Case 2 source-readback
theorem, the selected-entry residual readout has the expected fixed-pivot
inverse on the nonzero-pivot sector.

This is an open punctured-sector readout package.  It is not a measure
pushforward, determinant-chart Haar transport, source-prior comparison,
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq_preimageOfPivotNeZero_residualReadout_eq
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [TopologicalSpace η] [Fintype τ] [DecidableEq τ]
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
    (z₀ : η × (case2ResidualBlockPivotEntries n S (J + 1) → ℝ))
    (hCtop₀ : IsUnit ((Ctop z₀.1).det))
    (hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det)) :
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
          RetainedPassiveNonredundantCoordinateData
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
    ∃ U : Set (η × (center → ℝ)),
      IsOpen U ∧ z₀ ∈ U ∧
        ∀ z ∈ U,
          let E :=
            paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
              (fun p : Fin 2 ↦
                (sourceChart z p :
                  reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
          sourceChart z ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
            sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
              retainedData z ∧
            ∀ _ : z.2 pivotNext ≠ 0,
              SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
                pivotNext
                (fun i : center ↦
                  AoyagiResidualBlockCoordinateIndex.value
                    (residualFactorProduct
                      (sourceReadback
                        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E).C
                      (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)))
                    (residualCoordEquiv.symm i)) =
                z.2 := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv
  rcases
      (by
        simpa [center, EdgeFamily, retainedData, sourceChart] using
          exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            A1passive F2 A3passive Ctop F3
            hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
            z₀ hCtop₀ hA1passive₀) with
    ⟨U, hUopen, hz₀U, hUread⟩
  refine ⟨U, hUopen, hz₀U, ?_⟩
  intro z hz
  let E :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
      (fun p : Fin 2 ↦
        (sourceChart z p :
          reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
  have hbase := hUread z.1 z.2 hz
  have hlocal :
      sourceChart z ∈
        paperEndpointFixedBaseRetainedPassiveP13LocalSource
          W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) := hbase.1
  have hread :
      sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
        retainedData z := by
    simpa [E] using hbase.2
  refine ⟨hlocal, hread, ?_⟩
  intro hpivot
  let product :=
    residualFactorProduct
      (sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E).C
      (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))
  have hproduct :
      product =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c :
              AoyagiResidualBlockCoordinateIndex
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
              (residualCoordEquiv c)) := by
    dsimp [product]
    rw [hread]
    simpa [retainedData, center, pivotNext, residualCoordEquiv] using
      case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
        (ρ := Fin (Module.finrank ℝ U₀))
        n hS hcont hnext (A1passive z.1) (F2 z.1)
        (A3passive z.1) (Ctop z.1) (F3 z.1) z.2 eNext e
  have hreadout :
      (fun i : center ↦
        AoyagiResidualBlockCoordinateIndex.value product
          (residualCoordEquiv.symm i)) =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2 := by
    funext i
    rw [hproduct]
    calc
      AoyagiResidualBlockCoordinateIndex.value
          (AoyagiResidualBlockCoordinateIndex.matrix
            (fun c :
                AoyagiResidualBlockCoordinateIndex
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ↦
              SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
                (residualCoordEquiv c)))
          (residualCoordEquiv.symm i) =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
          (residualCoordEquiv (residualCoordEquiv.symm i)) := by
          simpa using
            congrFun
              (AoyagiResidualBlockCoordinateIndex.value_matrix
                (fun c :
                    AoyagiResidualBlockCoordinateIndex
                      (throughSubspaceEndpointComplementIndex
                        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
                      (throughSubspaceEndpointComplementIndex
                        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ↦
                  SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2
                    (residualCoordEquiv c)))
              (residualCoordEquiv.symm i)
      _ = SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2 i := by
        rw [Equiv.apply_symm_apply]
  change
    SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
        (fun i : center ↦
          AoyagiResidualBlockCoordinateIndex.value product
            (residualCoordEquiv.symm i)) =
      z.2
  rw [hreadout]
  exact
    SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap
      pivotNext z.2 hpivot

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
