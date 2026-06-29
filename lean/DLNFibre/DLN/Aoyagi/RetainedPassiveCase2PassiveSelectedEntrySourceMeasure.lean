import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySource
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure

/-!
# Retained-passive Case 2 passive selected-entry source measure support

This file turns the local determinant-domain source/readback theorem for the
passive selected-entry Case 2 chart into support of a chart-produced measure
after restricting the source-domain measure to that open determinant domain.
It does not prove source-image coverage, source-prior transport,
determinant-chart Haar transport, a Jacobian theorem, normal crossings, pole
order, or RLCT.
-/

noncomputable section

open MeasureTheory

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
coordinates are units, every chart-produced source measure restricted to the
resulting open determinant domain is supported on the retained-passive p.13
local source.

The support statement is only for the restricted source-domain measure
`sourceMeasure.restrict U`.  The source chart's a.e. measurability is derived
from continuity on `U`, using the determinant-chart subtype source-chart
continuity.  This is not source-image coverage, source-prior transport,
determinant-chart Haar transport, a Jacobian comparison, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_open_measure_map_case2EndpointTransport_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ η : Type} [TopologicalSpace η] [MeasurableSpace η]
    [OpensMeasurableSpace η] [Fintype τ] [DecidableEq τ]
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
    (hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det))
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
        (∀ z ∈ U,
          sourceChart z ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
            (let E :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p : Fin 2 ↦
                  (sourceChart z p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
              retainedData z)) ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            let μ := Measure.map sourceChart (sourceMeasure.restrict U)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            μ.restrict localSource = μ := by
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
  rcases
      (by
        simpa [center, EdgeFamily, retainedData, sourceChart] using
          exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            A1passive F2 A3passive Ctop F3
            hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
            z₀ hCtop₀ hA1passive₀) with
    ⟨U, hUopen, hz₀U, hUmem_readback_raw⟩
  have hUmem_readback :
      ∀ z ∈ U,
        sourceChart z ∈
            paperEndpointFixedBaseRetainedPassiveP13LocalSource
              W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
          (let E :=
            paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
              (fun p : Fin 2 ↦
                (sourceChart z p :
                  reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
          sourceReadback (K := ℝ) (ρ := ρ) E = retainedData z) := by
    intro z hz
    simpa [center, EdgeFamily, retainedData, sourceChart, ρ] using
      hUmem_readback_raw z.1 z.2 hz
  refine ⟨U, hUopen, hz₀U, ?_, ?_⟩
  · intro z hz
    simpa [ρ] using hUmem_readback z hz
  · intro _ _ _ μ localSource
    have hdet_of_mem :
        ∀ z ∈ U, (retainedData z).detChart := by
      intro z hz
      let E :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (sourceChart z p :
              reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
      have hlocal :
          sourceChart z ∈
            paperEndpointFixedBaseRetainedPassiveP13LocalSource
              W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) :=
        (hUmem_readback z hz).1
      have hEset :
          E ∈ sourceRecursiveDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
        simpa [E, paperEndpointFixedBaseRetainedPassiveP13LocalSource,
          ρ, κ'] using hlocal
      have hEchart :
          sourceRecursiveDetChart (K := ℝ) (ρ := ρ) E :=
        (mem_sourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ') E).1 hEset
      have hread :
          sourceReadback (K := ℝ) (ρ := ρ) E = retainedData z := by
        simpa [E, ρ] using (hUmem_readback z hz).2
      have hdet_readback :
          (sourceReadback (K := ℝ) (ρ := ρ) E).detChart :=
        sourceReadback_detChart_of_sourceRecursiveDetChart
          (K := ℝ) (ρ := ρ) E hEchart
      simpa [hread] using hdet_readback
    have hsourceContOn : ContinuousOn sourceChart U := by
      rw [continuousOn_iff_continuous_restrict]
      let DetData :=
        {data :
          RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' //
          data.detChart}
      let toDetChart : U → DetData :=
        fun z ↦ ⟨retainedData z.1, hdet_of_mem z.1 z.2⟩
      have hToDetChart : Continuous toDetChart := by
        have hamb :
            Continuous (fun z : U ↦ retainedData z.1) :=
          hretained.comp continuous_subtype_val
        exact hamb.subtype_mk _
      have hchart :
          Continuous
            (fun data : DetData ↦
              paperEndpointFixedBaseRetainedPassiveP13SourceChart
                W₂ B₂ U₀ hU₀ data) :=
        continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
          (K := ℝ) W₂ B₂ U₀ hU₀
      simpa [sourceChart, toDetChart, DetData,
        paperEndpointFixedBaseRetainedPassiveP13SourceChart,
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData] using
        hchart.comp hToDetChart
    have hsourceChart :
        AEMeasurable sourceChart (sourceMeasure.restrict U) :=
      ContinuousOn.aemeasurable₀ hsourceContOn
        hUopen.measurableSet.nullMeasurableSet
    have hchart_mem :
        ∀ᵐ z ∂ sourceMeasure.restrict U, sourceChart z ∈ localSource := by
      filter_upwards [ae_restrict_mem hUopen.measurableSet] with z hz
      exact (hUmem_readback z hz).1
    simpa [μ, localSource] using
      measure_map_restrict_retainedPassiveP13LocalSource_eq_self_of_ae_mem
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := fun E : EdgeFamily ↦ E)
        (η := sourceMeasure.restrict U) (sourceChart := sourceChart)
        (by simpa [EdgeFamily] using
          (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
        hsourceChart hchart_mem

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
