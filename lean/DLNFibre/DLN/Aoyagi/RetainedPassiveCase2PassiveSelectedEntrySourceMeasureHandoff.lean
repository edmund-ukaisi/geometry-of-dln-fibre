import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure

/-!
# Retained-passive Case 2 punctured-sector residual-source handoff

This file packages the chart-produced punctured-sector readout measure theorem
as a residual-source socket.  It transfers explicitly supplied positivity and
negative-power integrability of the residual-coordinate marginal to the
chart-produced retained-passive source measure.  It does not construct those
marginal hypotheses for an arbitrary source measure, and it does not prove
determinant-chart Haar transport, source-prior transport, a Jacobian formula,
normal crossings, pole order, or RLCT extraction.
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
/-- On the retained-passive Case 2 determinant-and-pivot-nonzero sector,
explicit residual marginal hypotheses give the retained-passive residual-source
hypotheses for the chart-produced source measure.

The marginal hypotheses are assumptions on
`Measure.map Prod.snd (sourceMeasure.restrict V)`.  The theorem does not prove
them for an arbitrary `sourceMeasure`, and it is not determinant-chart Haar
transport, source-prior transport, a passive Jacobian theorem, source-image
coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_marginal
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
    (hpivot₀ :
      z₀.2
        (⟨(J + 2, J + 2),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0)
    (sourceMeasure :
      Measure
        (η ×
          ({p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)))
    (t : ℝ) :
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
    ∃ V : Set (η × (center → ℝ)),
      IsOpen V ∧ z₀ ∈ V ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            let μ := Measure.map sourceChart (sourceMeasure.restrict V)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            let marginal := Measure.map Prod.snd (sourceMeasure.restrict V)
            μ.restrict localSource = μ ∧
              ((∀ᵐ y ∂ marginal,
                  0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext y) →
                (∫⁻ y : center → ℝ,
                  ENNReal.ofReal
                    ((SelectedEntrySignedBox.CenterCoord.residual pivotNext y) ^ (-t))
                    ∂ marginal) < ∞ →
                (∀ᵐ E ∂ μ.restrict localSource,
                    0 < aoyagiCoordinateSquareSum
                      (paperEndpointFixedBaseResidualBlockCoordinateMap
                        (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
                  residualNegPowerIntegrableOn
                    (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                    (fun E : EdgeFamily ↦ E) localSource μ t) := by
  intro center pivotNext EdgeFamily retainedData sourceChart
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
  let inverseReadout : EdgeFamily → center → ℝ :=
    fun X ↦
      SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
        (fun i : center ↦
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) X
            (residualCoordEquiv.symm i))
  rcases
      (by
        simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
          residualCoordEquiv, inverseReadout] using
          exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            A1passive F2 A3passive Ctop F3
            hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
            z₀ hCtop₀ hA1passive₀ hpivot₀ sourceMeasure) with
    ⟨V, hVopen, hz₀V, _hVpoint, hmeasure⟩
  refine ⟨V, hVopen, hz₀V, ?_⟩
  intro _ _ _ μ localSource marginal
  have hmeasure_local :
      μ.restrict localSource = μ ∧
        Measure.map inverseReadout μ = marginal := by
    simpa [μ, localSource, marginal] using hmeasure
  rcases hmeasure_local with ⟨hsupport, hmap⟩
  refine ⟨hsupport, ?_⟩
  intro hmarginal_pos hmarginal_finite
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let residualBase :
      EdgeFamily →
        AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) → ℝ :=
    fun E ↦
      paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
  let residualMap : EdgeFamily → center → ℝ :=
    fun E i ↦ residualBase E (residualCoordEquiv.symm i)
  have hEdgeMatrix :
      Measurable (fun E : EdgeFamily ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (E p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))) := by
    simpa [EdgeFamily] using
      (paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuous
        (K := ℝ) W₂ B₂ U₀ hU₀).measurable
  have hresidualBase_meas :
      Measurable
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)) :=
    measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
      (W := W₂) (B := B₂) U₀ hU₀ (fun E : EdgeFamily ↦ E) hEdgeMatrix
  have hresidualMap : Measurable residualMap := by
    refine measurable_pi_lambda _ ?_
    intro i
    have hi :
        Measurable (fun E : EdgeFamily ↦
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
            (residualCoordEquiv.symm i)) :=
      (measurable_pi_apply (residualCoordEquiv.symm i)).comp hresidualBase_meas
    simpa [residualMap, residualBase] using hi
  have hinverseReadout : Measurable inverseReadout := by
    have hpre :
        Measurable
          (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext) :=
      SelectedEntrySignedBox.CenterCoord.measurable_preimageOfPivotNeZero pivotNext
    simpa [inverseReadout, residualMap, residualBase] using hpre.comp hresidualMap
  have hselectedResidual_meas :
      Measurable
        (fun y : center → ℝ ↦
          SelectedEntrySignedBox.CenterCoord.residual pivotNext y) := by
    have hfun :
        (fun y : center → ℝ ↦
          SelectedEntrySignedBox.CenterCoord.residual pivotNext y) =
            fun y : center → ℝ ↦
              aoyagiCoordinateSquareSum
                (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext y) := by
      funext y
      rw [SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap]
    rw [hfun]
    exact
      measurable_aoyagiCoordinateSquareSum
        (SelectedEntrySignedBox.CenterCoord.measurable_chartMap pivotNext)
  have htargetIntegrand_meas :
      Measurable (fun y : center → ℝ ↦
        ENNReal.ofReal
          ((SelectedEntrySignedBox.CenterCoord.residual pivotNext y) ^ (-t))) := by
    fun_prop
  have hpos_map :
      ∀ᵐ y ∂ Measure.map inverseReadout μ,
        0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext y := by
    simpa [hmap] using hmarginal_pos
  have hpos_inverse :
      ∀ᵐ E ∂ μ,
        0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext
          (inverseReadout E) :=
    ae_of_ae_map hinverseReadout.aemeasurable hpos_map
  have hsquare_eq_of_inverse_pos :
      ∀ E : EdgeFamily,
        0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext
            (inverseReadout E) →
          aoyagiCoordinateSquareSum (residualBase E) =
            SelectedEntrySignedBox.CenterCoord.residual pivotNext
              (inverseReadout E) := by
    intro E hpos
    have hpivot_value : residualMap E pivotNext ≠ 0 := by
      intro hpivot_zero
      have hvalue_pivot_zero :
          paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E
              (residualCoordEquiv.symm pivotNext) = 0 := by
        simpa [residualMap, residualBase] using hpivot_zero
      have hinv_pivot_zero : inverseReadout E pivotNext = 0 := by
        simpa [inverseReadout, hvalue_pivot_zero,
          SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero]
      have hchart_zero :
          SelectedEntrySignedBox.CenterCoord.chartMap pivotNext
              (inverseReadout E) = 0 :=
        SelectedEntrySignedBox.CenterCoord.chartMap_eq_zero_of_pivot_eq_zero
          pivotNext (inverseReadout E) hinv_pivot_zero
      have hres_zero :
          SelectedEntrySignedBox.CenterCoord.residual pivotNext
              (inverseReadout E) = 0 := by
        rw [SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap,
          hchart_zero]
        simp [aoyagiCoordinateSquareSum]
      exact (ne_of_gt hpos) hres_zero
    have hchart :
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext
            (inverseReadout E) =
          residualMap E := by
      calc
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext
            (inverseReadout E) =
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext
              (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
                pivotNext (residualMap E)) := by
          simp [inverseReadout, residualMap, residualBase]
        _ = residualMap E :=
          SelectedEntrySignedBox.CenterCoord.chartMap_preimageOfPivotNeZero
            pivotNext (residualMap E) hpivot_value
    have hres_eq :
        SelectedEntrySignedBox.CenterCoord.residual pivotNext
            (inverseReadout E) =
          aoyagiCoordinateSquareSum (residualMap E) := by
      rw [SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap,
        hchart]
    have hsq_reindex :
        aoyagiCoordinateSquareSum (residualMap E) =
          aoyagiCoordinateSquareSum (residualBase E) := by
      simpa [residualMap, residualBase] using
        aoyagiCoordinateSquareSum_comp_equiv residualCoordEquiv.symm (residualBase E)
    calc
      aoyagiCoordinateSquareSum (residualBase E) =
          aoyagiCoordinateSquareSum (residualMap E) := hsq_reindex.symm
      _ = SelectedEntrySignedBox.CenterCoord.residual pivotNext
            (inverseReadout E) := hres_eq.symm
  have hpos_source :
      ∀ᵐ E ∂ μ,
        0 < aoyagiCoordinateSquareSum (residualBase E) :=
    hpos_inverse.mono fun E hE ↦ by
      have hsq := hsquare_eq_of_inverse_pos E hE
      rw [hsq]
      exact hE
  have hpos_source_local :
      ∀ᵐ E ∂ μ.restrict localSource,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E) := by
    simpa [hsupport, residualBase, κ'] using hpos_source
  have hfinite_inverse :
      (∫⁻ E : EdgeFamily,
        ENNReal.ofReal
          ((SelectedEntrySignedBox.CenterCoord.residual pivotNext
            (inverseReadout E)) ^ (-t)) ∂ μ) < ∞ := by
    have hfinite_map :
        (∫⁻ y : center → ℝ,
          ENNReal.ofReal
            ((SelectedEntrySignedBox.CenterCoord.residual pivotNext y) ^ (-t))
            ∂ Measure.map inverseReadout μ) < ∞ := by
      simpa [hmap] using hmarginal_finite
    rw [← lintegral_map htargetIntegrand_meas hinverseReadout]
    exact hfinite_map
  have hfinite_source :
      (∫⁻ E : EdgeFamily,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualBase E)) ^ (-t))
          ∂ μ) < ∞ := by
    have hlintegral :
        (∫⁻ E : EdgeFamily,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualBase E)) ^ (-t))
            ∂ μ) =
          (∫⁻ E : EdgeFamily,
            ENNReal.ofReal
              ((SelectedEntrySignedBox.CenterCoord.residual pivotNext
                (inverseReadout E)) ^ (-t)) ∂ μ) := by
      apply lintegral_congr_ae
      exact hpos_inverse.mono fun E hE ↦ by
        have hsq := hsquare_eq_of_inverse_pos E hE
        change
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (residualBase E)) ^ (-t)) =
            ENNReal.ofReal
              ((SelectedEntrySignedBox.CenterCoord.residual pivotNext
                (inverseReadout E)) ^ (-t))
        rw [hsq]
    exact hlintegral.trans_lt hfinite_inverse
  have hfinite_source_local :
      residualNegPowerIntegrableOn
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
        (fun E : EdgeFamily ↦ E) localSource μ t := by
    simpa [residualNegPowerIntegrableOn, hsupport, residualBase, κ'] using
      hfinite_source
  exact ⟨hpos_source_local, hfinite_source_local⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- For the concrete passive-product selected-entry coordinate measure, finite
passive mass and the selected-entry critical inequality supply the
punctured-sector residual-source hypotheses.

The proof uses only domination of the restricted residual-coordinate marginal
by the unrestricted product marginal; it does not assert equality after sector
restriction, determinant-chart Haar transport, source-prior transport, a
passive Jacobian formula, source-image coverage, normal crossings, pole order,
or RLCT extraction. -/
theorem exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass
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
    (hpivot₀ :
      z₀.2
        (⟨(J + 2, J + 2),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0)
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
      Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure : Measure (η × (center → ℝ)) :=
      passiveMeasure.prod weightedBox
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
    ∃ V : Set (η × (center → ℝ)),
      IsOpen V ∧ z₀ ∈ V ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            let μ := Measure.map sourceChart (sourceMeasure.restrict V)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            μ.restrict localSource = μ ∧
              (∀ᵐ E ∂ μ.restrict localSource,
                  0 < aoyagiCoordinateSquareSum
                    (paperEndpointFixedBaseResidualBlockCoordinateMap
                      (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
                residualNegPowerIntegrableOn
                  (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                  (fun E : EdgeFamily ↦ E) localSource μ t := by
  intro center pivotNext signedBox weightedBox sourceMeasure EdgeFamily retainedData sourceChart
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure,
          EdgeFamily, retainedData, sourceChart] using
          exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_marginal
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            A1passive F2 A3passive Ctop F3
            hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
            z₀ hCtop₀ hA1passive₀ hpivot₀ sourceMeasure t) with
    ⟨V, hVopen, hz₀V, hsocket⟩
  refine ⟨V, hVopen, hz₀V, ?_⟩
  intro _ _ _ μ localSource
  have hsocket_local :
      μ.restrict localSource = μ ∧
        ((∀ᵐ y ∂ Measure.map Prod.snd (sourceMeasure.restrict V),
            0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext y) →
          (∫⁻ y : center → ℝ,
            ENNReal.ofReal
              ((SelectedEntrySignedBox.CenterCoord.residual pivotNext y) ^ (-t))
              ∂ Measure.map Prod.snd (sourceMeasure.restrict V)) < ∞ →
          (∀ᵐ E ∂ μ.restrict localSource,
              0 < aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
            residualNegPowerIntegrableOn
              (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
              (fun E : EdgeFamily ↦ E) localSource μ t) := by
    simpa [μ, localSource, sourceMeasure] using hsocket
  rcases hsocket_local with ⟨hsupport, hresidual⟩
  have hmarginal_le :
      Measure.map Prod.snd (sourceMeasure.restrict V) ≤
        passiveMeasure Set.univ • weightedBox := by
    calc
      Measure.map Prod.snd (sourceMeasure.restrict V) ≤
          Measure.map Prod.snd sourceMeasure := by
        exact Measure.map_mono Measure.restrict_le_self measurable_snd
      _ = passiveMeasure Set.univ • weightedBox := by
        simp [sourceMeasure]
  have hbox :
      (∀ᵐ y ∂ weightedBox,
          0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext y) ∧
        (∫⁻ y : center → ℝ,
          ENNReal.ofReal
            ((SelectedEntrySignedBox.CenterCoord.residual pivotNext y) ^ (-t))
            ∂ weightedBox) < ∞ := by
    simpa [center, pivotNext, signedBox, weightedBox] using
      SelectedEntrySignedBox.CenterCoord.residual_pos_ae_and_lintegral_rpow_neg_withDensity_sourceDensity
        pivotNext ht hRres hcrit
  have hmarginal_pos :
      ∀ᵐ y ∂ Measure.map Prod.snd (sourceMeasure.restrict V),
        0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext y :=
    ae_of_measure_le_smul hmarginal_le hbox.1
  have hmarginal_finite :
      (∫⁻ y : center → ℝ,
        ENNReal.ofReal
          ((SelectedEntrySignedBox.CenterCoord.residual pivotNext y) ^ (-t))
          ∂ Measure.map Prod.snd (sourceMeasure.restrict V)) < ∞ :=
    lintegral_lt_top_of_measure_le_smul
      hmarginal_le hpassive_lt_top hbox.2
  exact ⟨hsupport, hresidual hmarginal_pos hmarginal_finite⟩

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
