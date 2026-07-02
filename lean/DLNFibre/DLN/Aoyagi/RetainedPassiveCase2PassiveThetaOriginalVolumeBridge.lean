import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaFormalProductSourceReference
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge

/-!
# Case 2 passive-theta source chart to original-volume bridge

This file composes the concrete Case 2 passive-theta raw-order/source-chart
package with the p.13 raw-order original-volume measure bridge.

The main theorem keeps the remaining passive-theta raw-pushforward identity as
an explicit hypothesis.  It does not prove determinant-chart Haar transport,
raw-order Haar transport, original source-prior transport, source-image
coverage, source-rank coverage, normal crossings, pole order, or RLCT
extraction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open DLNFibre.Core
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
/-- Conditional original-volume identity for the concrete Case 2 passive-theta
endpoint source chart.

If the local passive-theta raw-order map pushes `thetaReference.restrict V`
exactly to the raw-order source-recursive restriction of a raw Haar measure,
then the direct passive-theta endpoint source chart pushes
`thetaReference.restrict V` to the original edge-family volume restricted to
the named p.13 source set, up to the existing full-space Haar scalar.

The raw-pushforward identity is a hypothesis.  This theorem does not prove
determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet_of_rawMap_eq_restrict_rawSource
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
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
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
            Measure.map rawMap (thetaReference.restrict V) =
              rawHaar.restrict rawSourceSet →
              Measure.map sourceChart (thetaReference.restrict V) =
                ((Measure.map
                  (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                    W₂ B₂ U₀)
                  rawHaar).addHaarScalarFactor (originalTupleVolume d)) •
                    originalVolume.restrict p13SourceSet := by
  intro RawTuple EdgeFamily sourceChart rawMap rawSourceSet p13SourceSet d originalVolume
  let rawChart : RawTuple → EdgeFamily :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W₂ B₂ U₀ hU₀
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, _hpoint, hmeasure_maps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar hraw_push
  have htwo_stage :
      Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)) =
        Measure.map sourceChart (thetaReference.restrict V) := by
    have hmaps := hmeasure_maps (sourceMeasure := thetaReference)
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawChart] using hmaps.2
  have hraw_original :
      Measure.map rawChart (rawHaar.restrict rawSourceSet) =
        ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W₂ B₂ U₀)
          rawHaar).addHaarScalarFactor (originalTupleVolume d)) •
            originalVolume.restrict p13SourceSet := by
    simpa [RawTuple, EdgeFamily, rawChart, rawSourceSet, p13SourceSet,
      originalVolume, d] using
      DLNFibre.DLN.Aoyagi.map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) rawHaar
  calc
    Measure.map sourceChart (thetaReference.restrict V) =
        Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)) := by
          exact htwo_stage.symm
    _ = Measure.map rawChart (rawHaar.restrict rawSourceSet) := by
          rw [hraw_push]
    _ =
        ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W₂ B₂ U₀)
          rawHaar).addHaarScalarFactor (originalTupleVolume d)) •
            originalVolume.restrict p13SourceSet := hraw_original

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement records the honest forward direction of raw domination.
/-- Forward original-volume domination from a dominated raw-order pushforward.

If the local passive-theta raw-order image is only dominated by a scalar
multiple of raw Haar restricted to the raw-order source-recursive determinant
chart, then the concrete source-chart image is dominated by the corresponding
scalar multiple of the restricted original edge-family volume.

This is the forward comparison
`source image <= constant * original volume`.  It is not the reverse
comparison needed to read back original edge-family volume to the theta source
measure, and it does not remove the raw-pushforward equality hypothesis from
the finite-integral theorem. -/
theorem exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_le_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet_of_rawMap_le_smul_restrict_rawSource
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
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ thetaReference :
          Measure
            (Case2PassiveTheta
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure] {C : ℝ≥0∞},
            Measure.map rawMap (thetaReference.restrict V) ≤
              C • rawHaar.restrict rawSourceSet →
              let cHaar :=
                ((Measure.map
                  (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                    W₂ B₂ U₀)
                  rawHaar).addHaarScalarFactor (originalTupleVolume d))
              Measure.map sourceChart (thetaReference.restrict V) ≤
                (C * ((cHaar : NNReal) : ℝ≥0∞)) •
                  originalVolume.restrict p13SourceSet := by
  intro RawTuple EdgeFamily sourceChart rawMap rawSourceSet p13SourceSet d
    originalVolume
  let rawChart : RawTuple → EdgeFamily :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W₂ B₂ U₀ hU₀
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, _hpoint, hmeasure_maps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar C hraw_dom cHaar
  have hrawChart :
      AEMeasurable rawChart (rawHaar.restrict rawSourceSet) := by
    simpa [RawTuple, EdgeFamily, rawChart, rawSourceSet] using
      aemeasurable_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_rawSourceSet
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) rawHaar
  have hmap_le :
      Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)) ≤
        C • Measure.map rawChart (rawHaar.restrict rawSourceSet) :=
    map_le_smul_map_of_le_smul_aemeasurable hrawChart hraw_dom
  have htwo_stage :
      Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)) =
        Measure.map sourceChart (thetaReference.restrict V) := by
    have hmaps := hmeasure_maps (sourceMeasure := thetaReference)
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawChart] using hmaps.2
  have hsource_le :
      Measure.map sourceChart (thetaReference.restrict V) ≤
        C • Measure.map rawChart (rawHaar.restrict rawSourceSet) := by
    simpa [RawTuple, EdgeFamily, htwo_stage] using hmap_le
  have hraw_original :
      Measure.map rawChart (rawHaar.restrict rawSourceSet) =
        cHaar • originalVolume.restrict p13SourceSet := by
    simpa [RawTuple, EdgeFamily, rawChart, rawSourceSet, p13SourceSet,
      originalVolume, d, cHaar] using
      DLNFibre.DLN.Aoyagi.map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) rawHaar
  have hraw_original_le :
      Measure.map rawChart (rawHaar.restrict rawSourceSet) ≤
        ((cHaar : NNReal) : ℝ≥0∞) •
          originalVolume.restrict p13SourceSet := by
    simp [hraw_original]
  exact measure_le_smul_of_le_smul_of_le_smul hsource_le hraw_original_le

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the endpoint chart and p.13 source-measure interfaces.
/-- Same-shrink original-volume domination from formal-product/source-image
domination.

On a local Case 2 passive-theta source-chart image, if the p.13 formal-product
chart measure on a measurable chart piece is dominated by the chart-produced
source reference, then the restricted original edge-family volume on that
chart piece is dominated by the same source reference with the inverse p.13
Haar scalar.

The formal-product/source-image domination is a hypothesis.  This theorem does
not prove the missing local change-of-variables/source-coverage/lower-density
comparison, raw-Haar transport, source-prior transport, normal crossings, pole
order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_same_shrink_of_formalProductMeasure_le_smul_sourceReference
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
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let p13SourceChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        MeasurableSet (sourceChart '' V) ∧
          (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
            ∀ (m : Measure RawTuple) [m.IsAddHaarMeasure],
            ∀ thetaReference :
              Measure
                (Case2PassiveTheta
                  (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
            ∀ chartPiece : Set EdgeFamily,
            ∀ {D : ℝ≥0∞},
              MeasurableSet chartPiece →
                chartPiece ⊆ sourceChart '' V →
                  let sourceRef :=
                    Measure.map sourceChart (thetaReference.restrict V)
                  let formalProductMeasure : Measure EdgeFamily :=
                    Measure.map
                      (fun z : RawTuple ↦
                        p13SourceChart
                          (topologyTupleEdgeRawOrder
                            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                            (κ' := throughSubspaceEndpointComplementIndex
                              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z))
                      ((m.restrict rawDetChart).withDensity
                        (fun z : RawTuple ↦
                          ENNReal.ofReal
                            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                              (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                              (κ' := throughSubspaceEndpointComplementIndex
                                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z)))
                  formalProductMeasure.restrict chartPiece ≤ D • sourceRef →
                    let cHaar :=
                      ((Measure.map
                        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                          W₂ B₂ U₀)
                        m).addHaarScalarFactor (originalTupleVolume d))
                    originalVolume.restrict chartPiece ≤
                      ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) • sourceRef) := by
  intro RawTuple EdgeFamily sourceChart rawDetChart p13SourceSet d
    originalVolume p13SourceChart
  rcases
      (by
        simpa [EdgeFamily, p13SourceSet] using
          exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, _hdetV, _hleftV, _hsource_inj,
      _hsource_contOn, hsource_image, _hpoint, himage_p13⟩
  have himage_p13_compact : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, Case2PassiveTheta.A1passive,
      Case2PassiveTheta.F2, Case2PassiveTheta.A3passive,
      Case2PassiveTheta.Ctop, Case2PassiveTheta.F3,
      Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hVG, hsource_image, himage_p13_compact, ?_⟩
  intro m _instM thetaReference chartPiece D hchartPiece hchartPiece_sub_image
    sourceRef formalProductMeasure hformal_dom cHaar
  have hchartPiece_sub_p13 : chartPiece ⊆ p13SourceSet := by
    intro E hE
    exact himage_p13_compact E (hchartPiece_sub_image hE)
  simpa [RawTuple, EdgeFamily, rawDetChart, p13SourceSet, d, originalVolume,
    p13SourceChart, sourceChart, sourceRef, formalProductMeasure, cHaar] using
    DLNFibre.DLN.Aoyagi.originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure
      (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀) m
      hchartPiece
      (by simpa [p13SourceSet] using hchartPiece_sub_p13)
      (sourceRef := sourceRef) (D := D) hformal_dom

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in
-- The proof composes the with-following constant-density handoff with the p.13 source-measure bridge.
/-- Conditional with-following original-volume domination from the
constant-density formal-product/source-reference handoff.

After one local shrink, if the enlarged passive-theta raw-order map pushes the
chosen theta reference to raw Haar restricted to the raw-order
source-recursive chart, then every measurable p.13 chart piece contained in
the actual source-chart image is dominated by the enlarged source-image
reference, with the inverse tuple-side Haar scalar.

The raw-pushforward equality, chart-piece measurability, source-image
membership, and p.13 source-set membership remain explicit hypotheses.  This
does not prove raw Haar transport, source-image coverage, original-prior
transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
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
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
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
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ thetaReference :
          Measure
            (Case2PassiveThetaWithFollowingFactor
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
          MeasurableSet chartPiece →
            chartPiece ⊆ sourceChart '' V →
              chartPiece ⊆ p13SourceSet →
                Measure.map rawMap (thetaReference.restrict V) =
                  rawHaar.restrict rawSourceSet →
                  let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
                  let cHaar :=
                    ((Measure.map
                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                        W₂ B₂ U₀)
                      rawHaar).addHaarScalarFactor (originalTupleVolume d))
                  originalVolume.restrict chartPiece ≤
                    ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * (1 : ℝ≥0∞)) •
                      sourceRef) := by
  intro RawTuple EdgeFamily sourceChart rawMap rawSourceSet
    p13SourceSet d originalVolume
  rcases
      exists_open_subset_formalProductMeasure_restrict_chartPiece_eq_withDensity_one_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hformal⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_image hchartPiece_p13 hraw_push sourceRef cHaar
  let rawDetChart : Set RawTuple :=
    topologyTupleDetChartSet
      (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
  let rawChart : RawTuple → EdgeFamily :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W₂ B₂ U₀ hU₀
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
  let oneDensity : EdgeFamily → ℝ≥0∞ := fun _ ↦ 1
  simpa [RawTuple, EdgeFamily, rawDetChart, p13SourceSet, d, originalVolume,
    rawChart, sourceChart, formalProductMeasure, sourceRef, oneDensity,
    cHaar] using
    DLNFibre.DLN.Aoyagi.originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_eq_withDensity_bounded
      (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀) rawHaar
      hchartPiece (by simpa [p13SourceSet] using hchartPiece_p13)
      (sourceRef := sourceRef) (formalDensity := oneDensity) (D := (1 : ℝ≥0∞))
      (by
        exact (hformal thetaReference rawHaar chartPiece hchartPiece
          hchartPiece_p13 hraw_push).1)
      (by
        exact (hformal thetaReference rawHaar chartPiece hchartPiece
          hchartPiece_p13 hraw_push).2)

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This theorem discharges p.13 chart-piece support from local source-image support.
/-- Conditional with-following original-volume domination on source-image
chart pieces, with p.13 support discharged internally.

After one local shrink, if the enlarged passive-theta raw-order map pushes the
chosen theta reference to raw Haar restricted to the raw-order
source-recursive chart, then every measurable chart piece contained in the
actual source-chart image is dominated by the enlarged source-image reference,
with the inverse tuple-side Haar scalar.

The raw-pushforward equality, chart-piece measurability, and source-image
membership remain explicit hypotheses.  The p.13 chart-piece containment is
derived from local source-image support.  This does not prove raw Haar
transport, source-image coverage beyond this local image, original-prior
transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource_of_chartPiece_subset_sourceImage
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
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
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
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
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
          ∀ thetaReference :
            Measure
              (Case2PassiveThetaWithFollowingFactor
                (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
          ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
          ∀ chartPiece : Set EdgeFamily,
            MeasurableSet chartPiece →
              chartPiece ⊆ sourceChart '' V →
                Measure.map rawMap (thetaReference.restrict V) =
                  rawHaar.restrict rawSourceSet →
                  let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
                  let cHaar :=
                    ((Measure.map
                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                        W₂ B₂ U₀)
                      rawHaar).addHaarScalarFactor (originalTupleVolume d))
                  originalVolume.restrict chartPiece ≤
                    ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * (1 : ℝ≥0∞)) •
                      sourceRef) := by
  intro RawTuple EdgeFamily sourceChart rawMap rawSourceSet
    p13SourceSet d originalVolume
  rcases
      (by
        simpa [EdgeFamily, sourceChart, p13SourceSet] using
          exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V₀, hV₀open, hz₀V₀, hV₀G, _hdetV₀, _hleftV₀, _hsource_inj₀,
      _hsource_contOn₀, _hsource_image₀, hpoint₀, _himage_p13₀⟩
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
          p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ V₀ hV₀open hz₀V₀) with
    ⟨V, hVopen, hz₀V, hVV₀, hvolume_bridge⟩
  have hVG : V ⊆ G := fun z hz ↦ hV₀G (hVV₀ hz)
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    have hzV₀ : z ∈ V₀ := hVV₀ hzV
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hpoint₀ z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hzV₀
  refine ⟨V, hVopen, hz₀V, hVG, himage_p13V, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_image hraw_push sourceRef cHaar
  have hchartPiece_p13 : chartPiece ⊆ p13SourceSet := by
    intro E hE
    exact himage_p13V E (hchartPiece_image hE)
  simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
    p13SourceSet, d, originalVolume, sourceRef, cHaar] using
    hvolume_bridge thetaReference rawHaar chartPiece hchartPiece
      hchartPiece_image hchartPiece_p13 hraw_push

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The enlarged with-following chart has the same inverse-Haar p.13 density
-- identity once the exact raw-source pushforward is supplied.
/-- Conditional inverse-Haar density identity for original edge-family volume
over a concrete enlarged Case 2 passive-theta source reference.

If the local with-following passive-theta raw-order map pushes
`thetaReference.restrict V` exactly to the raw-order source-recursive
restriction of a raw Haar measure, then on every measurable p.13 chart piece
the restricted original edge-family volume is a constant inverse-Haar-density
perturbation of the enlarged chart-produced source reference.

The raw-pushforward identity is a hypothesis.  This theorem does not prove
determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
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
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
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
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ thetaReference :
          Measure
            (Case2PassiveThetaWithFollowingFactor
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
          MeasurableSet chartPiece →
            chartPiece ⊆ p13SourceSet →
              Measure.map rawMap (thetaReference.restrict V) =
                rawHaar.restrict rawSourceSet →
                let c :=
                  ((Measure.map
                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                      W₂ B₂ U₀)
                    rawHaar).addHaarScalarFactor (originalTupleVolume d))
                let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
                let invHaarDensity : EdgeFamily → ℝ≥0∞ :=
                  fun _ ↦ ((c⁻¹ : NNReal) : ℝ≥0∞)
                originalVolume.restrict chartPiece =
                    (sourceRef.withDensity invHaarDensity).restrict chartPiece ∧
                  (∀ᵐ E ∂sourceRef.restrict chartPiece,
                    invHaarDensity E ≤ ((c⁻¹ : NNReal) : ℝ≥0∞)) := by
  intro RawTuple EdgeFamily sourceChart rawMap rawSourceSet
    p13SourceSet d originalVolume
  rcases
      exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hpoint, hmeasure_maps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_sub hraw_push c sourceRef invHaarDensity
  let rawChart : RawTuple → EdgeFamily :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W₂ B₂ U₀ hU₀
  have htwo_stage :
      Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)) =
        Measure.map sourceChart (thetaReference.restrict V) := by
    have hmaps := hmeasure_maps (sourceMeasure := thetaReference)
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawChart] using hmaps.2
  have hraw_original :
      Measure.map rawChart (rawHaar.restrict rawSourceSet) =
        ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W₂ B₂ U₀)
          rawHaar).addHaarScalarFactor (originalTupleVolume d)) •
            originalVolume.restrict p13SourceSet := by
    simpa [RawTuple, EdgeFamily, rawChart, rawSourceSet, p13SourceSet,
      originalVolume, d] using
      DLNFibre.DLN.Aoyagi.map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) rawHaar
  have hsource_whole :
      sourceRef = c • originalVolume.restrict p13SourceSet := by
    calc
      sourceRef =
          Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)) := by
            exact htwo_stage.symm
      _ = Measure.map rawChart (rawHaar.restrict rawSourceSet) := by
            rw [hraw_push]
      _ = c • originalVolume.restrict p13SourceSet := by
            simpa [c] using hraw_original
  have hsource_piece :
      sourceRef.restrict chartPiece = c • originalVolume.restrict chartPiece := by
    calc
      sourceRef.restrict chartPiece =
          (c • originalVolume.restrict p13SourceSet).restrict chartPiece := by
            rw [hsource_whole]
      _ = c • (originalVolume.restrict p13SourceSet).restrict chartPiece := by
            rw [Measure.restrict_smul]
      _ = c • originalVolume.restrict chartPiece := by
            rw [Measure.restrict_restrict_of_subset hchartPiece_sub]
  let L : RawTuple ≃L[ℝ] Tuple (k := ℝ) d :=
    paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv W₂ B₂ U₀
  haveI : Measure.IsAddHaarMeasure (Measure.map L rawHaar) :=
    L.isAddHaarMeasure_map rawHaar
  haveI : Measure.IsAddHaarMeasure (originalTupleVolume d) :=
    isAddHaarMeasure_originalTupleVolume d
  have hc_pos : 0 < c := by
    simpa [c, L] using
      MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
        (Measure.map L rawHaar) (originalTupleVolume d)
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hvolume_inv :
      originalVolume.restrict chartPiece = c⁻¹ • sourceRef.restrict chartPiece :=
    measure_eq_inv_smul_of_eq_nnreal_smul
      (μ := sourceRef.restrict chartPiece)
      (ν := originalVolume.restrict chartPiece) (c := c) hc_ne hsource_piece
  constructor
  · calc
      originalVolume.restrict chartPiece =
          c⁻¹ • sourceRef.restrict chartPiece := hvolume_inv
      _ = (sourceRef.withDensity invHaarDensity).restrict chartPiece := by
            simp [invHaarDensity, withDensity_const, Measure.restrict_smul]
  · exact Filter.Eventually.of_forall fun _ ↦ le_rfl

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Same-shrink source-image version of the exact inverse-Haar density bridge.
/-- Conditional inverse-Haar density identity on the actual local
with-following source-image chart.

This strengthens the p.13 chart-piece bridge by using one local shrink `V` for
the source-chart image package and the raw-order/source-chart measure handoff.
If the local with-following passive-theta raw-order map pushes
`thetaReference.restrict V` exactly to the raw-order source-recursive
restriction of a raw Haar measure, then on every measurable chart piece
contained in `sourceChart '' V`, the restricted original edge-family volume is
a constant inverse-Haar-density perturbation of the source-image reference
`Measure.map sourceChart (thetaReference.restrict V)`.

The raw-pushforward identity is a hypothesis.  This theorem does not prove
determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage beyond this local chart,
source-rank coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
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
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
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
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ thetaReference :
                  Measure
                    (Case2PassiveThetaWithFollowingFactor
                      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      Measure.map rawMap (thetaReference.restrict V) =
                        rawHaar.restrict rawSourceSet →
                        let c :=
                          ((Measure.map
                            (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                              W₂ B₂ U₀)
                            rawHaar).addHaarScalarFactor (originalTupleVolume d))
                        let sourceRef :=
                          Measure.map sourceChart (thetaReference.restrict V)
                        let invHaarDensity : EdgeFamily → ℝ≥0∞ :=
                          fun _ ↦ ((c⁻¹ : NNReal) : ℝ≥0∞)
                        originalVolume.restrict chartPiece =
                            (sourceRef.withDensity invHaarDensity).restrict chartPiece ∧
                          (∀ᵐ E ∂sourceRef.restrict chartPiece,
                            invHaarDensity E ≤ ((c⁻¹ : NNReal) : ℝ≥0∞)) := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawSourceSet
    p13SourceSet d originalVolume
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback, p13SourceSet] using
          exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V₀, hV₀open, hz₀V₀, hV₀G, _hdetV₀, hleftV₀, hsource_inj₀,
      hsource_contOn₀, _hsource_image₀, hpoint₀, _himage_p13₀⟩
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
          p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ V₀ hV₀open hz₀V₀) with
    ⟨V, hVopen, hz₀V, hVV₀, hexact_bridge⟩
  have hVG : V ⊆ G := fun z hz ↦ hV₀G (hVV₀ hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hzV₀ : z ∈ V₀ := hVV₀ hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ V₀ := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hzV₀
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV₀ z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  have hsource_inj : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    exact hsource_inj₀ (hVV₀ hz) (hVV₀ hz') hsrc
  have hsource_contOn : ContinuousOn sourceChart V :=
    hsource_contOn₀.mono hVV₀
  have hsource_image : MeasurableSet (sourceChart '' V) :=
    hVopen.measurableSet.image_of_continuousOn_injOn hsource_contOn hsource_inj
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    have hzV₀ : z ∈ V₀ := hVV₀ hzV
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hpoint₀ z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hzV₀
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_contOn,
      hsource_image, himage_p13V, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_image hraw_push c sourceRef invHaarDensity
  have hchartPiece_p13 : chartPiece ⊆ p13SourceSet := by
    intro E hE
    exact himage_p13V E (hchartPiece_image hE)
  simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
    p13SourceSet, d, originalVolume, c, sourceRef, invHaarDensity] using
    hexact_bridge thetaReference rawHaar chartPiece hchartPiece
      hchartPiece_p13 hraw_push

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The enlarged statement replaces exact raw-source pushforward by reverse
-- raw-source domination, matching the non-following bridge.
/-- Same-shrink with-following original-volume domination from reverse
raw-source domination.

On a local enlarged Case 2 passive-theta source chart, if raw Haar restricted
to the raw-order source-recursive chart is dominated by a scalar multiple of
the local with-following raw-order image, then the restricted original
edge-family volume on any measurable p.13 chart piece is dominated by the
local source-chart image, with the inverse tuple-side Haar scalar multiplied
in front.

The reverse raw-source domination is an explicit hypothesis.  This theorem
does not prove determinant-chart Haar transport, full raw Haar transport,
original source-prior transport, source-image coverage, source-rank coverage,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
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
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
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
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ thetaReference :
          Measure
            (Case2PassiveThetaWithFollowingFactor
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
        ∀ {D : ℝ≥0∞},
          MeasurableSet chartPiece →
            chartPiece ⊆ p13SourceSet →
              rawHaar.restrict rawSourceSet ≤
                D • Measure.map rawMap (thetaReference.restrict V) →
                let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
                let cHaar :=
                  ((Measure.map
                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                      W₂ B₂ U₀)
                    rawHaar).addHaarScalarFactor (originalTupleVolume d))
                originalVolume.restrict chartPiece ≤
                  ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) • sourceRef) := by
  intro RawTuple EdgeFamily sourceChart rawMap rawSourceSet
    p13SourceSet d originalVolume
  let p13SourceChart : RawTuple → EdgeFamily :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W₂ B₂ U₀ hU₀
  let rawDetChart : Set RawTuple :=
    topologyTupleDetChartSet
      (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
  rcases
      exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hformal_dom⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece D hchartPiece
    hchartPiece_sub hraw_dom sourceRef cHaar
  let formalProductMeasure : Measure EdgeFamily :=
    Measure.map
      (fun z : RawTuple ↦
        p13SourceChart
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
  have hformal_source :
      formalProductMeasure.restrict chartPiece ≤ D • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawDetChart,
      rawSourceSet, p13SourceSet, p13SourceChart, formalProductMeasure,
      sourceRef] using
      hformal_dom thetaReference rawHaar chartPiece hchartPiece_sub hraw_dom
  simpa [RawTuple, EdgeFamily, rawDetChart, p13SourceSet, d, originalVolume,
    p13SourceChart, sourceChart, sourceRef, formalProductMeasure, cHaar] using
    DLNFibre.DLN.Aoyagi.originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure
      (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀) rawHaar
      hchartPiece
      (by simpa [p13SourceSet] using hchartPiece_sub)
      (sourceRef := sourceRef) (D := D) hformal_source

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Localized with-following original-volume domination from a chart-piece raw patch.
/-- Same-shrink with-following original-volume domination from localized
reverse raw-source domination.

On a local enlarged Case 2 passive-theta source chart, if raw Haar restricted
to a raw patch `P` is dominated by a scalar multiple of the local
with-following raw-order image, and `P` contains the raw preimage of the p.13
chart piece inside the raw source set, then the restricted original
edge-family volume on that chart piece is dominated by the local source-chart
image, with the inverse tuple-side Haar scalar multiplied in front.

The localized reverse raw-source domination is an explicit hypothesis.  This
theorem does not prove determinant-chart Haar transport, full raw Haar
transport, original source-prior transport, source-image coverage, source-rank
coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_patch_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
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
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
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
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)
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
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ thetaReference :
          Measure
            (Case2PassiveThetaWithFollowingFactor
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
        ∀ P : Set RawTuple,
        ∀ {D : ℝ≥0∞},
          MeasurableSet chartPiece →
            chartPiece ⊆ p13SourceSet →
              P ⊆ rawSourceSet →
                rawSourceSet ∩ rawChart ⁻¹' chartPiece ⊆ P →
                  rawHaar.restrict P ≤
                    D • Measure.map rawMap (thetaReference.restrict V) →
                  let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
                  let cHaar :=
                    ((Measure.map
                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                        W₂ B₂ U₀)
                      rawHaar).addHaarScalarFactor (originalTupleVolume d))
                  originalVolume.restrict chartPiece ≤
                    ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) • sourceRef) := by
  intro RawTuple EdgeFamily sourceChart rawMap rawSourceSet
    p13SourceSet rawChart d originalVolume
  let rawDetChart : Set RawTuple :=
    topologyTupleDetChartSet
      (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
  rcases
      exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_patch_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hformal_dom⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece P D hchartPiece
    hchartPiece_sub hP_sub hrawPatch_sub hraw_dom sourceRef cHaar
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
  have hformal_source :
      formalProductMeasure.restrict chartPiece ≤ D • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawDetChart,
      rawSourceSet, p13SourceSet, rawChart, formalProductMeasure,
      sourceRef] using
      hformal_dom thetaReference rawHaar chartPiece P hchartPiece
        hchartPiece_sub hP_sub hrawPatch_sub hraw_dom
  simpa [RawTuple, EdgeFamily, rawDetChart, p13SourceSet, d, originalVolume,
    rawChart, sourceChart, sourceRef, formalProductMeasure, cHaar] using
    DLNFibre.DLN.Aoyagi.originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure
      (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀) rawHaar
      hchartPiece
      (by simpa [p13SourceSet] using hchartPiece_sub)
      (sourceRef := sourceRef) (D := D) hformal_source

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the endpoint chart and p.13 source-measure interfaces.
/-- Same-shrink original-volume domination from reverse raw-source domination.

On a local Case 2 passive-theta source chart, if raw Haar restricted to the
raw-order source-recursive chart is dominated by a scalar multiple of the local
passive-theta raw-order image, then the restricted original edge-family volume
on any measurable p.13 chart piece is dominated by the local source-chart image,
with the inverse tuple-side Haar scalar multiplied in front.

The reverse raw-source domination is an explicit hypothesis.  This theorem
does not prove determinant-chart Haar transport, full raw Haar transport,
original source-prior transport, source-image coverage, source-rank coverage,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
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
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
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
          MeasurableSet chartPiece →
            chartPiece ⊆ p13SourceSet →
              rawHaar.restrict rawSourceSet ≤
                D • Measure.map rawMap (thetaReference.restrict V) →
                let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
                let cHaar :=
                  ((Measure.map
                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                      W₂ B₂ U₀)
                    rawHaar).addHaarScalarFactor (originalTupleVolume d))
                originalVolume.restrict chartPiece ≤
                  ((((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D) • sourceRef) := by
  intro RawTuple EdgeFamily sourceChart rawMap rawSourceSet
    p13SourceSet d originalVolume
  let p13SourceChart : RawTuple → EdgeFamily :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W₂ B₂ U₀ hU₀
  let rawDetChart : Set RawTuple :=
    topologyTupleDetChartSet
      (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
  rcases
      exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hformal_dom⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece D hchartPiece
    hchartPiece_sub hraw_dom sourceRef cHaar
  let formalProductMeasure : Measure EdgeFamily :=
    Measure.map
      (fun z : RawTuple ↦
        p13SourceChart
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
  have hformal_source :
      formalProductMeasure.restrict chartPiece ≤ D • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawDetChart,
      rawSourceSet, p13SourceSet, p13SourceChart, formalProductMeasure,
      sourceRef] using
      hformal_dom thetaReference rawHaar chartPiece hchartPiece_sub hraw_dom
  simpa [RawTuple, EdgeFamily, rawDetChart, p13SourceSet, d, originalVolume,
    p13SourceChart, sourceChart, sourceRef, formalProductMeasure, cHaar] using
    DLNFibre.DLN.Aoyagi.originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceMeasure_of_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece_le_smul_sourceMeasure
      (W := W₂) (B := B₂) (M := 1) (U₀ := U₀) (hU₀ := hU₀) rawHaar
      hchartPiece
      (by simpa [p13SourceSet] using hchartPiece_sub)
      (sourceRef := sourceRef) (D := D) hformal_source

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the endpoint chart and p.13 source-measure interfaces.
/-- Conditional inverse-Haar density identity for original edge-family volume
over a concrete Case 2 passive-theta source reference.

If the local passive-theta raw-order map pushes `thetaReference.restrict V`
exactly to the raw-order source-recursive restriction of a raw Haar measure,
then on every measurable p.13 chart piece the restricted original edge-family
volume is a constant inverse-Haar-density perturbation of the concrete
passive-theta chart-produced source reference.

The raw-pushforward identity is a hypothesis.  This theorem does not prove
determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceReference_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
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
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
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
                let c :=
                  ((Measure.map
                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                      W₂ B₂ U₀)
                    rawHaar).addHaarScalarFactor (originalTupleVolume d))
                let sourceRef := Measure.map sourceChart (thetaReference.restrict V)
                let invHaarDensity : EdgeFamily → ℝ≥0∞ :=
                  fun _ ↦ ((c⁻¹ : NNReal) : ℝ≥0∞)
                originalVolume.restrict chartPiece =
                    (sourceRef.withDensity invHaarDensity).restrict chartPiece ∧
                  (∀ᵐ E ∂sourceRef.restrict chartPiece,
                    invHaarDensity E ≤ ((c⁻¹ : NNReal) : ℝ≥0∞)) := by
  intro RawTuple EdgeFamily sourceChart rawMap rawSourceSet p13SourceSet d originalVolume
  rcases
      exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet_of_rawMap_eq_restrict_rawSource
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hsource_eq⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece hchartPiece_sub hraw_push
    c sourceRef invHaarDensity
  have hsource_whole :
      sourceRef = c • originalVolume.restrict p13SourceSet := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet, p13SourceSet,
      d, originalVolume, c, sourceRef] using
      hsource_eq thetaReference rawHaar hraw_push
  have hsource_piece :
      sourceRef.restrict chartPiece = c • originalVolume.restrict chartPiece := by
    calc
      sourceRef.restrict chartPiece =
          (c • originalVolume.restrict p13SourceSet).restrict chartPiece := by
            rw [hsource_whole]
      _ = c • (originalVolume.restrict p13SourceSet).restrict chartPiece := by
            rw [Measure.restrict_smul]
      _ = c • originalVolume.restrict chartPiece := by
            rw [Measure.restrict_restrict_of_subset hchartPiece_sub]
  let L : RawTuple ≃L[ℝ] Tuple (k := ℝ) d :=
    paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv W₂ B₂ U₀
  haveI : Measure.IsAddHaarMeasure (Measure.map L rawHaar) :=
    L.isAddHaarMeasure_map rawHaar
  haveI : Measure.IsAddHaarMeasure (originalTupleVolume d) :=
    isAddHaarMeasure_originalTupleVolume d
  have hc_pos : 0 < c := by
    simpa [c, L] using
      MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
        (Measure.map L rawHaar) (originalTupleVolume d)
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hvolume_inv :
      originalVolume.restrict chartPiece = c⁻¹ • sourceRef.restrict chartPiece :=
    measure_eq_inv_smul_of_eq_nnreal_smul
      (μ := sourceRef.restrict chartPiece)
      (ν := originalVolume.restrict chartPiece) (c := c) hc_ne hsource_piece
  constructor
  · calc
      originalVolume.restrict chartPiece =
          c⁻¹ • sourceRef.restrict chartPiece := hvolume_inv
      _ = (sourceRef.withDensity invHaarDensity).restrict chartPiece := by
            simp [invHaarDensity, withDensity_const, Measure.restrict_smul]
  · exact Filter.Eventually.of_forall fun _ ↦ le_rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement keeps the raw-Haar pushforward as an explicit hypothesis.
/-- Conditional inverse-Haar density identity on the actual local source-image
chart for the concrete Case 2 passive-theta source chart.

This strengthens the preceding bridge by using one local shrink `V` for both
the source-chart image package and the raw-order/source-chart measure handoff.
If the local passive-theta raw-order map pushes `thetaReference.restrict V`
exactly to the raw-order source-recursive restriction of a raw Haar measure,
then on every measurable chart piece contained in the actual image
`sourceChart '' V`, the restricted original edge-family volume is a constant
inverse-Haar-density perturbation of the concrete source-image reference
`Measure.map sourceChart (thetaReference.restrict V)`.

The raw-pushforward identity is a hypothesis.  This theorem does not prove
determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
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
    [T2Space
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
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
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
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                ∀ thetaReference :
                  Measure
                    (Case2PassiveTheta
                      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                ∀ chartPiece : Set EdgeFamily,
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      Measure.map rawMap (thetaReference.restrict V) =
                        rawHaar.restrict rawSourceSet →
                        let c :=
                          ((Measure.map
                            (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                              W₂ B₂ U₀)
                            rawHaar).addHaarScalarFactor (originalTupleVolume d))
                        let sourceRef :=
                          Measure.map sourceChart (thetaReference.restrict V)
                        let invHaarDensity : EdgeFamily → ℝ≥0∞ :=
                          fun _ ↦ ((c⁻¹ : NNReal) : ℝ≥0∞)
                        originalVolume.restrict chartPiece =
                            (sourceRef.withDensity invHaarDensity).restrict chartPiece ∧
                          (∀ᵐ E ∂sourceRef.restrict chartPiece,
                            invHaarDensity E ≤ ((c⁻¹ : NNReal) : ℝ≥0∞)) := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawSourceSet
    p13SourceSet d originalVolume
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let retainedData :
      Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
    fun theta ↦
      case2PassiveThetaEndpointRetainedData
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
  let Y :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  let rawChart : RawTuple → EdgeFamily :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W₂ B₂ U₀ hU₀
  let inverseReadout : EdgeFamily → case2ResidualBlockPivotEntries n S (J + 1) → ℝ :=
    case2PassiveThetaEndpointInverseReadout
      W₂ B₂ n hS hnext hU₀ eNext e
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, hmeasure_maps⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hread :
        let E :=
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              (sourceChart z p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
        sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
          retainedData z := by
      simpa [retainedData, sourceChart, rawMap, rawChart, inverseReadout, ρ, κ'] using
        (hpoint z hz).2.2.2.2.1
    have hinv : inverseReadout (sourceChart z) = z.yNext := by
      simpa [sourceChart, rawMap, rawChart, inverseReadout, ρ, κ'] using
        (hpoint z hz).2.2.2.2.2
    simpa [readback, sourceChart, retainedData, inverseReadout, ρ, κ'] using
      case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
        W₂ B₂ n hS hcont hnext hU₀ eNext e z (sourceChart z)
        hread hinv
  have hsource_inj : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    calc
      z = readback (sourceChart z) := (hleftV z hz).symm
      _ = readback (sourceChart z') := by rw [hsrc]
      _ = z' := hleftV z' hz'
  let detSet : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  have hdetV : ∀ z ∈ V, (retainedData z).detChart := by
    intro z hz
    have hYz : Y z ∈ detSet := by
      simpa [Y, detSet, RawTuple, ρ, κ'] using (hpoint z hz).1
    exact
      (topologyTuple_mem_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z)).1
        (by simpa [Y, detSet, retainedData, RawTuple, ρ, κ'] using hYz)
  have hretained_cont : Continuous retainedData := by
    simpa [retainedData, ρ, κ'] using
      continuous_case2PassiveThetaEndpointRetainedData
        (ρ := ρ) n hS hcont hnext eNext e
  have hsource_contOn : ContinuousOn sourceChart V := by
    rw [continuousOn_iff_continuous_restrict]
    let DetData :=
      {data : RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' //
        data.detChart}
    let toDetData : V → DetData := fun z ↦
      ⟨retainedData z.1, hdetV z.1 z.2⟩
    have htoDetData : Continuous toDetData := by
      have hval : Continuous (fun z : V ↦ retainedData z.1) :=
        hretained_cont.comp continuous_subtype_val
      exact hval.subtype_mk _
    have hsource :
        Continuous
          (fun data : DetData ↦
            paperEndpointFixedBaseRetainedPassiveP13SourceChart W₂ B₂ U₀ hU₀ data) :=
      continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    simpa [sourceChart, case2PassiveThetaEndpointSourceChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceChart,
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData,
      toDetData, retainedData, DetData, ρ, κ'] using
      hsource.comp htoDetData
  have hsource_image : MeasurableSet (sourceChart '' V) :=
    hVopen.measurableSet.image_of_continuousOn_injOn hsource_contOn hsource_inj
  have himage_p13 : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hz, rfl⟩
    have hlocal := (hpoint z hz).2.2.2.1
    simpa [p13SourceSet,
      paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet] using
      hlocal
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_sub_image hraw_push c sourceRef invHaarDensity
  have hchartPiece_sub : chartPiece ⊆ p13SourceSet := fun E hE ↦
    himage_p13 E (hchartPiece_sub_image hE)
  have htwo_stage :
      Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)) =
        Measure.map sourceChart (thetaReference.restrict V) := by
    have hmaps := hmeasure_maps (sourceMeasure := thetaReference)
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawChart] using hmaps.2
  have hraw_original :
      Measure.map rawChart (rawHaar.restrict rawSourceSet) =
        ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W₂ B₂ U₀)
          rawHaar).addHaarScalarFactor (originalTupleVolume d)) •
            originalVolume.restrict p13SourceSet := by
    simpa [RawTuple, EdgeFamily, rawChart, rawSourceSet, p13SourceSet,
      originalVolume, d] using
      DLNFibre.DLN.Aoyagi.map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet
        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀) rawHaar
  have hsource_whole :
      sourceRef = c • originalVolume.restrict p13SourceSet := by
    calc
      sourceRef =
          Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V)) := by
            exact htwo_stage.symm
      _ = Measure.map rawChart (rawHaar.restrict rawSourceSet) := by
            rw [hraw_push]
      _ = c • originalVolume.restrict p13SourceSet := by
            simpa [c] using hraw_original
  have hsource_piece :
      sourceRef.restrict chartPiece = c • originalVolume.restrict chartPiece := by
    calc
      sourceRef.restrict chartPiece =
          (c • originalVolume.restrict p13SourceSet).restrict chartPiece := by
            rw [hsource_whole]
      _ = c • (originalVolume.restrict p13SourceSet).restrict chartPiece := by
            rw [Measure.restrict_smul]
      _ = c • originalVolume.restrict chartPiece := by
            rw [Measure.restrict_restrict_of_subset hchartPiece_sub]
  let L : RawTuple ≃L[ℝ] Tuple (k := ℝ) d :=
    paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv W₂ B₂ U₀
  haveI : Measure.IsAddHaarMeasure (Measure.map L rawHaar) :=
    L.isAddHaarMeasure_map rawHaar
  haveI : Measure.IsAddHaarMeasure (originalTupleVolume d) :=
    isAddHaarMeasure_originalTupleVolume d
  have hc_pos : 0 < c := by
    simpa [c, L] using
      MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
        (Measure.map L rawHaar) (originalTupleVolume d)
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hvolume_inv :
      originalVolume.restrict chartPiece = c⁻¹ • sourceRef.restrict chartPiece :=
    measure_eq_inv_smul_of_eq_nnreal_smul
      (μ := sourceRef.restrict chartPiece)
      (ν := originalVolume.restrict chartPiece) (c := c) hc_ne hsource_piece
  constructor
  · calc
      originalVolume.restrict chartPiece =
          c⁻¹ • sourceRef.restrict chartPiece := hvolume_inv
      _ = (sourceRef.withDensity invHaarDensity).restrict chartPiece := by
            simp [invHaarDensity, withDensity_const, Measure.restrict_smul]
  · exact Filter.Eventually.of_forall fun _ ↦ le_rfl

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
