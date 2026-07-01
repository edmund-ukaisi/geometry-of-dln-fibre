import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure

/-!
# Case 2 passive-theta formal-product source-reference bridge

This file packages the p.13 formal-product chart measure as the concrete
Case 2 passive-theta chart-produced source reference, conditional on the
remaining raw-source pushforward identity.

The raw-pushforward identity is an explicit hypothesis.  The file does not
prove determinant-chart Haar transport, full raw Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction.
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
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the endpoint chart and p.13 source-measure interfaces.
/-- Conditional formal-product/source-reference restricted equality for the
concrete Case 2 passive-theta source chart.

If the local passive-theta raw-order map pushes `thetaReference.restrict V`
exactly to the raw-order source-recursive restriction of a raw Haar measure,
then on every p.13 chart piece the p.13 formal-product chart measure is the
concrete passive-theta chart-produced source reference after restriction.

The raw-pushforward identity is a hypothesis.  This theorem does not prove
determinant-chart Haar transport, full raw Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_formalProductMeasure_restrict_chartPiece_eq_sourceReference_restrict_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
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
    [MeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ thetaReference :
          Measure
            (Case2PassiveTheta
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
          chartPiece ⊆ p13SourceSet →
            Measure.map rawMap (thetaReference.restrict V) =
              rawHaar.restrict rawSourceSet →
              let formalProductMeasure : Measure EdgeFamily :=
                Measure.map
                  (fun z : RawTuple ↦
                    rawChart
                      (topologyTupleEdgeRawOrder
                        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                        (κ' := throughSubspaceEndpointComplementIndex
                          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z))
                  ((rawHaar.restrict rawDetChart).withDensity
                    (fun z : RawTuple ↦
                      ENNReal.ofReal
                        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                          (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                          (κ' := throughSubspaceEndpointComplementIndex
                            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z)))
              let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
              formalProductMeasure.restrict chartPiece =
                sourceRef.restrict chartPiece := by
  intro RawTuple EdgeFamily sourceChart rawMap rawDetChart rawSourceSet
    p13SourceSet rawChart
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, _hpoint, hmeasure_maps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece_sub
    hraw_push formalProductMeasure sourceRef
  have htwo_stage :
      Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)) =
        Measure.map sourceChart (thetaReference.restrict V) := by
    have hmaps := hmeasure_maps (sourceMeasure := thetaReference)
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawChart] using hmaps.2
  have hformal_whole :
      formalProductMeasure =
        (Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict
          p13SourceSet := by
    simpa [RawTuple, EdgeFamily, rawDetChart, p13SourceSet, rawChart,
      rawSourceSet, formalProductMeasure] using
      measure_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_eq_restrict_sourceEdgeFamilySet
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) rawHaar
  have hformal_source :
      formalProductMeasure = sourceRef.restrict p13SourceSet := by
    calc
      formalProductMeasure =
          (Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict
            p13SourceSet := hformal_whole
      _ =
          (Measure.map rawChart
            (Measure.map rawMap (thetaReference.restrict V))).restrict
            p13SourceSet := by
            rw [← hraw_push]
      _ = sourceRef.restrict p13SourceSet := by
            rw [htwo_stage]
  have hpiece :
      formalProductMeasure.restrict chartPiece = sourceRef.restrict chartPiece := by
    calc
      formalProductMeasure.restrict chartPiece =
          (sourceRef.restrict p13SourceSet).restrict chartPiece := by
            rw [hformal_source]
      _ = sourceRef.restrict chartPiece :=
            Measure.restrict_restrict_of_subset hchartPiece_sub
  exact hpiece

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the endpoint chart and p.13 source-measure interfaces.
/-- Conditional formal-product/source-reference domination for the concrete
Case 2 passive-theta source chart.

If raw Haar restricted to the raw-order source-recursive chart is dominated by
the local passive-theta raw-order image, then every p.13 chart piece of the
formal-product chart measure is dominated by the corresponding
passive-theta source-chart image with the same scalar.

The raw reverse-domination hypothesis is explicit.  This theorem does not
prove determinant-chart Haar transport, full raw Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
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
    [MeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ thetaReference :
          Measure
            (Case2PassiveTheta
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
        ∀ {D : ℝ≥0∞},
          chartPiece ⊆ p13SourceSet →
            rawHaar.restrict rawSourceSet ≤
              D • Measure.map rawMap (thetaReference.restrict V) →
              let formalProductMeasure : Measure EdgeFamily :=
                Measure.map
                  (fun z : RawTuple ↦
                    rawChart
                      (topologyTupleEdgeRawOrder
                        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                        (κ' := throughSubspaceEndpointComplementIndex
                          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z))
                  ((rawHaar.restrict rawDetChart).withDensity
                    (fun z : RawTuple ↦
                      ENNReal.ofReal
                        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                          (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                          (κ' := throughSubspaceEndpointComplementIndex
                            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z)))
              let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
              formalProductMeasure.restrict chartPiece ≤ D • sourceRef := by
  intro RawTuple EdgeFamily sourceChart rawMap rawDetChart rawSourceSet
    p13SourceSet rawChart
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, hmeasure_maps⟩
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let Y :
      Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        RawTuple :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
  have hdet_of_mem :
      ∀ z ∈ V, Y z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    intro z hz
    simpa [Y, RawTuple, ρ, κ'] using (hpoint z hz).1
  have hrawMapContOn : ContinuousOn rawMap V := by
    rw [continuousOn_iff_continuous_restrict]
    let Sdet : Set RawTuple :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let toDetTuple : V → Sdet :=
      fun z ↦ ⟨Y z.1, hdet_of_mem z.1 z.2⟩
    have hToDetTuple : Continuous toDetTuple := by
      have hamb : Continuous (fun z : V ↦ Y z.1) := by
        change Continuous
          (fun z : V ↦
            case2PassiveThetaEndpointTopologyTuple
              (ρ := ρ) n hS hcont hnext z.1 eNext e)
        exact
          (continuous_case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext eNext e).comp continuous_subtype_val
      exact hamb.subtype_mk _
    have hrawDet :
        Continuous
          (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ↦
            topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1) :=
      continuous_topologyTupleEdgeRawOrder_detChart_subtype
        (K := ℝ) (ρ := ρ) (κ' := κ')
    simpa [rawMap, Y, toDetTuple, Sdet, RawTuple, ρ, κ'] using
      hrawDet.comp hToDetTuple
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece D hchartPiece_sub hraw_dom
    formalProductMeasure sourceRef
  have hrawMap_aemeas :
      AEMeasurable rawMap (thetaReference.restrict V) :=
    ContinuousOn.aemeasurable₀ hrawMapContOn
      hVopen.measurableSet.nullMeasurableSet
  have hraw_mem :
      ∀ᵐ z ∂thetaReference.restrict V, rawMap z ∈ rawSourceSet := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    simpa [rawMap, rawSourceSet, RawTuple, ρ, κ'] using (hpoint z hz).2.1
  have hrawSourceSet_meas : MeasurableSet rawSourceSet := by
    simpa [rawSourceSet, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hraw_image_mem :
      ∀ᵐ y ∂Measure.map rawMap (thetaReference.restrict V),
        y ∈ rawSourceSet :=
    (ae_map_iff hrawMap_aemeas hrawSourceSet_meas).2 hraw_mem
  have hraw_image_support :
      (Measure.map rawMap (thetaReference.restrict V)).restrict rawSourceSet =
        Measure.map rawMap (thetaReference.restrict V) :=
    Measure.restrict_eq_self_of_ae_mem hraw_image_mem
  have hrawChart_source :
      AEMeasurable rawChart
        (Measure.map rawMap (thetaReference.restrict V)) := by
    have hrawChart_restrict :
        AEMeasurable rawChart
          ((Measure.map rawMap (thetaReference.restrict V)).restrict
            rawSourceSet) := by
      simpa [RawTuple, EdgeFamily, rawChart, rawSourceSet, ρ, κ'] using
        aemeasurable_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_rawSourceSet
          (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀)
          (Measure.map rawMap (thetaReference.restrict V))
    simpa [hraw_image_support] using hrawChart_restrict
  have hmap_le :
      Measure.map rawChart (rawHaar.restrict rawSourceSet) ≤
        D • Measure.map rawChart
          (Measure.map rawMap (thetaReference.restrict V)) :=
    map_le_smul_map_of_le_smul_aemeasurable hrawChart_source hraw_dom
  have htwo_stage :
      Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)) =
        Measure.map sourceChart (thetaReference.restrict V) := by
    have hmaps := hmeasure_maps (sourceMeasure := thetaReference)
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawChart] using hmaps.2
  have hformal_whole :
      formalProductMeasure =
        (Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict
          p13SourceSet := by
    simpa [RawTuple, EdgeFamily, rawDetChart, p13SourceSet, rawChart,
      rawSourceSet, formalProductMeasure] using
      measure_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_eq_restrict_sourceEdgeFamilySet
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) rawHaar
  have hformal_piece_eq :
      formalProductMeasure.restrict chartPiece =
        (Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict
          chartPiece := by
    calc
      formalProductMeasure.restrict chartPiece =
          ((Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict
            p13SourceSet).restrict chartPiece := by
            rw [hformal_whole]
      _ = (Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict
            chartPiece :=
            Measure.restrict_restrict_of_subset hchartPiece_sub
  have hformal_piece_le :
      formalProductMeasure.restrict chartPiece ≤
        Measure.map rawChart (rawHaar.restrict rawSourceSet) := by
    rw [hformal_piece_eq]
    exact
      (Measure.restrict_le_self :
        (Measure.map rawChart (rawHaar.restrict rawSourceSet)).restrict chartPiece ≤
          Measure.map rawChart (rawHaar.restrict rawSourceSet))
  have hmap_le_source :
      Measure.map rawChart (rawHaar.restrict rawSourceSet) ≤
        D • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceRef, htwo_stage] using hmap_le
  exact le_trans hformal_piece_le hmap_le_source

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the endpoint chart and p.13 source-measure interfaces.
/-- Conditional formal-product/source-reference identity for the concrete Case
2 passive-theta source chart, in the bounded-density socket shape.

If the local passive-theta raw-order map pushes `thetaReference.restrict V`
exactly to the raw-order source-recursive restriction of a raw Haar measure,
then on every measurable p.13 chart piece the p.13 formal-product chart
measure is the concrete passive-theta chart-produced source reference with
constant density `1`.

The raw-pushforward identity is a hypothesis.  This theorem does not prove
determinant-chart Haar transport, full raw Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_formalProductMeasure_restrict_chartPiece_eq_withDensity_one_sourceReference_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
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
    [MeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ thetaReference :
          Measure
            (Case2PassiveTheta
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
          MeasurableSet chartPiece →
            chartPiece ⊆ p13SourceSet →
              Measure.map rawMap (thetaReference.restrict V) =
                rawHaar.restrict rawSourceSet →
                let formalProductMeasure : Measure EdgeFamily :=
                  Measure.map
                    (fun z : RawTuple ↦
                      rawChart
                        (topologyTupleEdgeRawOrder
                          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                          (κ' := throughSubspaceEndpointComplementIndex
                            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z))
                    ((rawHaar.restrict rawDetChart).withDensity
                      (fun z : RawTuple ↦
                        ENNReal.ofReal
                          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                            (κ' := throughSubspaceEndpointComplementIndex
                              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z)))
                let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
                let oneDensity : EdgeFamily → ℝ≥0∞ := fun _ ↦ 1
                formalProductMeasure.restrict chartPiece =
                    (sourceRef.withDensity oneDensity).restrict chartPiece ∧
                  (∀ᵐ E ∂sourceRef.restrict chartPiece,
                    oneDensity E ≤ (1 : ℝ≥0∞)) := by
  intro RawTuple EdgeFamily sourceChart rawMap rawDetChart rawSourceSet
    p13SourceSet rawChart
  rcases
      exists_open_subset_formalProductMeasure_restrict_chartPiece_eq_sourceReference_restrict_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hdirect⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece _hchartPiece hchartPiece_sub
    hraw_push formalProductMeasure sourceRef oneDensity
  have hpiece :
      formalProductMeasure.restrict chartPiece = sourceRef.restrict chartPiece := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawDetChart, rawSourceSet,
      p13SourceSet, rawChart, formalProductMeasure, sourceRef] using
      hdirect thetaReference rawHaar chartPiece hchartPiece_sub hraw_push
  constructor
  · calc
      formalProductMeasure.restrict chartPiece =
          sourceRef.restrict chartPiece := hpiece
      _ = (sourceRef.withDensity oneDensity).restrict chartPiece := by
            simp [oneDensity]
  · exact Filter.Eventually.of_forall fun _ ↦ le_rfl

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
