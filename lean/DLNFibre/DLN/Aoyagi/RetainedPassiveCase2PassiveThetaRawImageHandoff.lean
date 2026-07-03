import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobianMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference

/-!
# Case 2 passive-theta raw-image density handoff

This file records the exact raw-image measure identity available for the
globally Jacobian-weighted passive-theta reference.  If the theta-side
Jacobian density factors through the local raw-order map, then the raw-order
pushforward is the raw image of the unweighted passive source with the
corresponding raw density.

This does not identify that raw image with additive Haar restricted to the
raw-order source set.  In particular, it does not prove determinant-chart Haar
transport from the passive-product theta measure, raw Haar normalization,
source-image coverage, source-rank coverage, normal crossings, pole order, or
RLCT extraction.
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
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the passive-theta chart and raw-order interfaces.
/-- Exact raw-image density formula for the concrete Case 2 passive-theta
raw-order map.

On a local determinant/pivot sector, let
`passiveSource = passiveMeasure.prod weightedBox` and let
`baseJ = passiveSource.withDensity jacobianDensity`, where `jacobianDensity`
is Aoyagi's retained-passive formal raw-order product determinant evaluated at
the endpoint topology tuple.  If this theta-side Jacobian density factors
almost everywhere through the raw-order map as a raw density, then the
pushforward of `baseJ.restrict V` is exactly the raw image of
`passiveSource.restrict V` weighted by that raw density.

The conclusion is over the actual raw image
`Measure.map rawMap (passiveSource.restrict V)`.  It is not a raw-Haar
pushforward theorem. -/
theorem exists_open_subset_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_eq_withDensity_rawImage_of_jacobianDensity_ae_eq
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
      (Case2PassiveTheta.PassiveFields
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
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ rawDensity : RawTuple → ℝ≥0∞,
          AEMeasurable rawDensity
              (Measure.map rawMap (passiveSource.restrict V)) →
            (∀ᵐ z ∂ passiveSource.restrict V,
              jacobianDensity z = rawDensity (rawMap z)) →
              Measure.map rawMap (baseJ.restrict V) =
                (Measure.map rawMap (passiveSource.restrict V)).withDensity
                  rawDensity := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple Y
    jacobianDensity baseJ rawMap
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, _hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawDensity hrawDensity hfactor
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
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
  have hrawMap :
      AEMeasurable rawMap (passiveSource.restrict V) := by
    exact
      ContinuousOn.aemeasurable₀ hrawMapContOn
        hVopen.measurableSet.nullMeasurableSet
  simpa [baseJ] using
    DLNFibre.DLN.Aoyagi.measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq
      (thetaMeasure := passiveSource) (V := V) (rawMap := rawMap)
      (thetaDensity := jacobianDensity) (rawDensity := rawDensity)
      hVopen.measurableSet hrawMap hrawDensity hfactor

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The enlarged with-following statement keeps the theta source measure
-- explicit; it only inserts a supplied raw density through the local raw map.
/-- Exact raw-image density formula for the enlarged Case 2 passive-theta
with-following raw-order map.

On a local determinant/pivot sector, let `baseJ` be an arbitrary
with-following source-domain measure weighted by Aoyagi's retained-passive
formal raw-order product determinant evaluated at the endpoint topology tuple.
If this theta-side density factors almost everywhere through the local
raw-order map as a supplied raw density, then pushing `baseJ.restrict V`
through the raw-order map is exactly the raw image of the unweighted restricted
source measure with that supplied raw density.

The conclusion is over the actual raw image
`Measure.map rawMap (sourceMeasure.restrict V)`.  It is not a raw-Haar
pushforward theorem and does not construct the density. -/
theorem exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_eq_withDensity_rawImage_of_jacobianDensity_ae_eq
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
    (sourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
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
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      sourceMeasure.withDensity jacobianDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ rawDensity : RawTuple → ℝ≥0∞,
          AEMeasurable rawDensity
              (Measure.map rawMap (sourceMeasure.restrict V)) →
            (∀ᵐ z ∂ sourceMeasure.restrict V,
              jacobianDensity z = rawDensity (rawMap z)) →
              Measure.map rawMap (baseJ.restrict V) =
                (Measure.map rawMap (sourceMeasure.restrict V)).withDensity
                  rawDensity := by
  intro RawTuple Y jacobianDensity baseJ rawMap
  rcases
      exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hpoint, _hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawDensity hrawDensity hfactor
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
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
            case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
              (ρ := ρ) n hS hcont hnext z.1 eNext e)
        exact
          (continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
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
  have hrawMap :
      AEMeasurable rawMap (sourceMeasure.restrict V) := by
    exact
      ContinuousOn.aemeasurable₀ hrawMapContOn
        hVopen.measurableSet.nullMeasurableSet
  simpa [baseJ] using
    DLNFibre.DLN.Aoyagi.measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq
      (thetaMeasure := sourceMeasure) (V := V) (rawMap := rawMap)
      (thetaDensity := jacobianDensity) (rawDensity := rawDensity)
      hVopen.measurableSet hrawMap hrawDensity hfactor

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The inverse-readback density is a concrete specialization of the conditional
-- raw-image handoff.  It still targets the actual raw image, not raw Haar.
/-- Concrete with-following raw-image density formula using raw-order inverse
readback.

This specializes
`exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_eq_withDensity_rawImage_of_jacobianDensity_ae_eq`
to the raw-side density obtained by evaluating the retained-passive formal
raw-order product determinant at `topologyTupleEdgeRawOrderInverse y`.

This is not the target-side inverse Jacobian density.  The conclusion is still
over the actual raw image `Measure.map rawMap (sourceMeasure.restrict V)`, not
over raw Haar restricted to the raw-order source set. -/
theorem exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_eq_withDensity_rawImage_rawOrderInverse_jacobianDensity
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
    (sourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
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
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      sourceMeasure.withDensity jacobianDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (topologyTupleEdgeRawOrderInverse
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y))
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        Measure.map rawMap (baseJ.restrict V) =
          (Measure.map rawMap (sourceMeasure.restrict V)).withDensity
            rawDensity := by
  intro RawTuple Y jacobianDensity baseJ rawMap rawDensity
  rcases
      exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hpoint, _hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let T : Set RawTuple :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
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
            case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
              (ρ := ρ) n hS hcont hnext z.1 eNext e)
        exact
          (continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
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
  have hrawMap :
      AEMeasurable rawMap (sourceMeasure.restrict V) := by
    exact
      ContinuousOn.aemeasurable₀ hrawMapContOn
        hVopen.measurableSet.nullMeasurableSet
  have hraw_mem :
      ∀ᵐ z ∂sourceMeasure.restrict V, rawMap z ∈ T := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    simpa [rawMap, T, RawTuple, ρ, κ'] using (hpoint z hz).2.1
  have hT_meas : MeasurableSet T := by
    simpa [T, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hraw_image_mem :
      ∀ᵐ y ∂Measure.map rawMap (sourceMeasure.restrict V), y ∈ T :=
    (ae_map_iff hrawMap hT_meas).2 hraw_mem
  have hrawDensityContOn : ContinuousOn rawDensity T := by
    rw [continuousOn_iff_continuous_restrict]
    rw [continuous_iff_continuousAt]
    intro y
    let invMap : T → RawTuple :=
      fun y ↦ topologyTupleEdgeRawOrderInverse
        (K := ℝ) (ρ := ρ) (κ' := κ') y.1
    have hInv :
        Continuous invMap :=
      continuous_topologyTupleEdgeRawOrderInverse_rawOrderSourceRecursiveDetChart_subtype
        (K := ℝ) (ρ := ρ) (κ' := κ')
    have hpre :
        invMap y ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
      simpa [invMap] using
        topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ') y.2
    have hreal :
        ContinuousAt
          (fun y : T ↦
            retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := 1) (ρ := ρ) (κ' := κ') (invMap y)) y :=
      (continuousAt_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_of_mem_topologyTupleDetChartSet
        (M := 1) (ρ := ρ) (κ' := κ') (invMap y) hpre).comp hInv.continuousAt
    simpa [rawDensity, invMap, RawTuple, ρ, κ'] using
      ENNReal.continuous_ofReal.continuousAt.comp hreal
  have hrawDensity_restrict :
      AEMeasurable rawDensity
        ((Measure.map rawMap (sourceMeasure.restrict V)).restrict T) :=
    ContinuousOn.aemeasurable₀ hrawDensityContOn hT_meas.nullMeasurableSet
  have hraw_restrict_eq :
      (Measure.map rawMap (sourceMeasure.restrict V)).restrict T =
        Measure.map rawMap (sourceMeasure.restrict V) :=
    Measure.restrict_eq_self_of_ae_mem hraw_image_mem
  have hrawDensity :
      AEMeasurable rawDensity
        (Measure.map rawMap (sourceMeasure.restrict V)) := by
    simpa [hraw_restrict_eq] using hrawDensity_restrict
  have hfactor :
      ∀ᵐ z ∂sourceMeasure.restrict V,
        jacobianDensity z = rawDensity (rawMap z) := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    have hInv :
        topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') (Y z)) =
          Y z :=
      topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := ρ) (κ' := κ') (hdet_of_mem z hz)
    simp [jacobianDensity, rawDensity, rawMap, RawTuple, ρ, κ', hInv]
  simpa [baseJ] using
    DLNFibre.DLN.Aoyagi.measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq
      (thetaMeasure := sourceMeasure) (V := V) (rawMap := rawMap)
      (thetaDensity := jacobianDensity) (rawDensity := rawDensity)
      hVopen.measurableSet hrawMap hrawDensity hfactor

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The enlarged statement transports a supplied determinant-chart forward
-- domination through the retained-passive raw-order COV theorem.
/-- Conditional determinant-Haar to raw-Haar domination for the
with-following Case 2 source measure.

On a local with-following determinant/pivot sector, suppose the endpoint
topology-tuple pushforward of the unweighted with-following source measure is
dominated by a scalar multiple of additive Haar restricted to the
retained-passive determinant chart.  Then the raw-order pushforward of
`baseJ = sourceMeasure.withDensity jacobianDensity` is dominated by the same
scalar multiple of additive Haar restricted to the raw-order source-recursive
determinant chart.

The determinant-chart domination hypothesis remains explicit.  This theorem
uses the retained-passive formal-product Jacobian change-of-variables theorem;
it does not prove source-prior transport, exact raw-Haar pushforward, raw-Haar
normalization, source-image/source-rank coverage, normal crossings, pole order,
or RLCT extraction. -/
theorem exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_le_smul_rawHaar_restrict_rawSource_of_endpointTopologyTuple_restrict_le_smul_detHaar
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
    (sourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
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
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      sourceMeasure.withDensity jacobianDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
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
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure] {c : ℝ≥0∞},
          Measure.map Y (sourceMeasure.restrict V) ≤
              c • rawHaar.restrict rawDetChart →
            Measure.map rawMap (baseJ.restrict V) ≤
              c • rawHaar.restrict rawSourceSet := by
  intro RawTuple Y jacobianDensity baseJ rawMap rawDetChart rawSourceSet
  rcases
      exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hpoint, _hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawHaar _instRawHaar c hYdom
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let Φ : RawTuple → RawTuple :=
    fun y ↦
      topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
  let formalDensity : RawTuple → ℝ≥0∞ :=
    fun y ↦
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := 1) (ρ := ρ) (κ' := κ') y)
  have hY :
      AEMeasurable Y (sourceMeasure.restrict V) := by
    have hYcont : Continuous Y := by
      simpa [Y, RawTuple, ρ, κ'] using
        continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hdet_nm :
      NullMeasurableSet rawDetChart rawHaar := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      nullMeasurableSet_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') rawHaar
  have hformalDensity_ref :
      AEMeasurable formalDensity (rawHaar.restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm
    intro y hy
    exact
      (ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_of_mem_topologyTupleDetChartSet
          (M := 1) (ρ := ρ) (κ' := κ') y (by
            simpa [rawDetChart, RawTuple, ρ, κ'] using hy))).continuousWithinAt
  have hΦ_ref :
      AEMeasurable Φ (rawHaar.restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ_ref_weighted :
      AEMeasurable Φ ((rawHaar.restrict rawDetChart).withDensity formalDensity) :=
    hΦ_ref.mono_ac (withDensity_absolutelyContinuous _ _)
  have hΦ_ref_map :
      Measure.map Φ ((rawHaar.restrict rawDetChart).withDensity formalDensity) =
        rawHaar.restrict rawSourceSet := by
    simpa [Φ, formalDensity, rawDetChart, rawSourceSet, RawTuple, ρ, κ'] using
      map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart
        (M := 1) (ρ := ρ) (κ' := κ') rawHaar hdet_nm
  have hbase_restrict :
      baseJ.restrict V =
        (sourceMeasure.restrict V).withDensity (fun z ↦ formalDensity (Y z)) := by
    change (sourceMeasure.withDensity jacobianDensity).restrict V =
      (sourceMeasure.restrict V).withDensity (fun z ↦ formalDensity (Y z))
    rw [restrict_withDensity hVopen.measurableSet]
  have hweighted :
      Measure.map (fun z ↦ Φ (Y z))
          ((sourceMeasure.restrict V).withDensity (fun z ↦ formalDensity (Y z))) ≤
        c • rawHaar.restrict rawSourceSet :=
    DLNFibre.DLN.Aoyagi.map_comp_withDensity_comp_le_smul_of_map_le_smul_of_weighted_map_ref_eq
      (μ := sourceMeasure.restrict V)
      (sourceRef := rawHaar.restrict rawDetChart)
      (targetRef := rawHaar.restrict rawSourceSet)
      (pre := Y) (post := Φ) (density := formalDensity)
      hY hformalDensity_ref hΦ_ref_weighted hYdom hΦ_ref_map
  calc
    Measure.map rawMap (baseJ.restrict V) =
        Measure.map rawMap
          ((sourceMeasure.restrict V).withDensity (fun z ↦ formalDensity (Y z))) := by
          rw [hbase_restrict]
    _ ≤ c • rawHaar.restrict rawSourceSet := by
          simpa [rawMap, Φ, RawTuple, ρ, κ'] using hweighted

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The enlarged statement transports a supplied determinant-chart reverse
-- domination through the retained-passive raw-order COV theorem.
/-- Conditional reverse determinant-Haar to raw-Haar domination for the
with-following Case 2 source measure.

On a local with-following determinant/pivot sector, suppose additive Haar
restricted to the retained-passive determinant chart is dominated by a scalar
multiple of the endpoint topology-tuple pushforward of the unweighted
with-following source measure.  Then additive Haar restricted to the raw-order
source-recursive determinant chart is dominated by the same scalar multiple of
the raw-order pushforward of
`baseJ = sourceMeasure.withDensity jacobianDensity`.

The determinant-chart reverse domination hypothesis remains explicit.  This
theorem uses the retained-passive formal-product Jacobian change-of-variables
theorem; it does not prove source-prior transport, exact raw-Haar pushforward,
raw-Haar normalization, source-image/source-rank coverage, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
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
    (sourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
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
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      sourceMeasure.withDensity jacobianDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
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
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        AEMeasurable rawMap (baseJ.restrict V) ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure] {c : ℝ≥0∞},
          rawHaar.restrict rawDetChart ≤
              c • Measure.map Y (sourceMeasure.restrict V) →
            rawHaar.restrict rawSourceSet ≤
              c • Measure.map rawMap (baseJ.restrict V) := by
  intro RawTuple Y jacobianDensity baseJ rawMap rawDetChart rawSourceSet
  rcases
      exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hpoint, _hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_, ?_⟩
  · let ρ := Fin (Module.finrank ℝ U₀)
    let κ' : Fin 3 → Type :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    have hdet_of_mem :
        ∀ z ∈ V,
          Y z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
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
              case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
                (ρ := ρ) n hS hcont hnext z.1 eNext e)
          exact
            (continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
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
    exact
      ContinuousOn.aemeasurable₀ hrawMapContOn
        hVopen.measurableSet.nullMeasurableSet
  intro rawHaar _instRawHaar c hYdom
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let Φ : RawTuple → RawTuple :=
    fun y ↦
      topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
  let formalDensity : RawTuple → ℝ≥0∞ :=
    fun y ↦
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := 1) (ρ := ρ) (κ' := κ') y)
  have hY :
      AEMeasurable Y (sourceMeasure.restrict V) := by
    have hYcont : Continuous Y := by
      simpa [Y, RawTuple, ρ, κ'] using
        continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hdet_meas : MeasurableSet rawDetChart := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hdet_nm_rawHaar :
      NullMeasurableSet rawDetChart rawHaar := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      nullMeasurableSet_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') rawHaar
  have hY_mem :
      ∀ᵐ z ∂sourceMeasure.restrict V, Y z ∈ rawDetChart := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    simpa [Y, rawDetChart, RawTuple, ρ, κ'] using (hpoint z hz).1
  have hmapY_mem :
      ∀ᵐ y ∂Measure.map Y (sourceMeasure.restrict V),
        y ∈ rawDetChart :=
    (ae_map_iff hY hdet_meas).2 hY_mem
  have hmapY_restrict :
      (Measure.map Y (sourceMeasure.restrict V)).restrict rawDetChart =
        Measure.map Y (sourceMeasure.restrict V) :=
    Measure.restrict_eq_self_of_ae_mem hmapY_mem
  have hdet_nm_mapY :
      NullMeasurableSet rawDetChart (Measure.map Y (sourceMeasure.restrict V)) :=
    hdet_meas.nullMeasurableSet
  have hformalDensity_map_restrict :
      AEMeasurable formalDensity
        ((Measure.map Y (sourceMeasure.restrict V)).restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm_mapY
    intro y hy
    exact
      (ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_of_mem_topologyTupleDetChartSet
          (M := 1) (ρ := ρ) (κ' := κ') y (by
            simpa [rawDetChart, RawTuple, ρ, κ'] using hy))).continuousWithinAt
  have hformalDensity_map :
      AEMeasurable formalDensity
        (Measure.map Y (sourceMeasure.restrict V)) := by
    simpa [hmapY_restrict] using hformalDensity_map_restrict
  have hΦ_map_restrict :
      AEMeasurable Φ
        ((Measure.map Y (sourceMeasure.restrict V)).restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm_mapY
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ_map :
      AEMeasurable Φ (Measure.map Y (sourceMeasure.restrict V)) := by
    simpa [hmapY_restrict] using hΦ_map_restrict
  have hΦ_map_weighted :
      AEMeasurable Φ
        ((Measure.map Y (sourceMeasure.restrict V)).withDensity
          formalDensity) :=
    hΦ_map.mono_ac (withDensity_absolutelyContinuous _ _)
  have hΦ_ref_map :
      Measure.map Φ ((rawHaar.restrict rawDetChart).withDensity formalDensity) =
        rawHaar.restrict rawSourceSet := by
    simpa [Φ, formalDensity, rawDetChart, rawSourceSet, RawTuple, ρ, κ'] using
      map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart
        (M := 1) (ρ := ρ) (κ' := κ') rawHaar hdet_nm_rawHaar
  have hbase_restrict :
      baseJ.restrict V =
        (sourceMeasure.restrict V).withDensity (fun z ↦ formalDensity (Y z)) := by
    change (sourceMeasure.withDensity jacobianDensity).restrict V =
      (sourceMeasure.restrict V).withDensity (fun z ↦ formalDensity (Y z))
    rw [restrict_withDensity hVopen.measurableSet]
  have hweighted :
      rawHaar.restrict rawSourceSet ≤
        c • Measure.map (fun z ↦ Φ (Y z))
          ((sourceMeasure.restrict V).withDensity
            (fun z ↦ formalDensity (Y z))) :=
    DLNFibre.DLN.Aoyagi.weighted_map_ref_le_smul_map_comp_withDensity_comp_of_le_smul_map
      (μ := sourceMeasure.restrict V)
      (sourceRef := rawHaar.restrict rawDetChart)
      (targetRef := rawHaar.restrict rawSourceSet)
      (pre := Y) (post := Φ) (density := formalDensity)
      hY hformalDensity_map hΦ_map_weighted hYdom hΦ_ref_map
  have htarget_eq :
      Measure.map (fun z ↦ Φ (Y z))
          ((sourceMeasure.restrict V).withDensity
            (fun z ↦ formalDensity (Y z))) =
        Measure.map rawMap (baseJ.restrict V) := by
    rw [hbase_restrict]
  calc
    rawHaar.restrict rawSourceSet ≤
        c • Measure.map (fun z ↦ Φ (Y z))
          ((sourceMeasure.restrict V).withDensity
            (fun z ↦ formalDensity (Y z))) := hweighted
    _ = c • Measure.map rawMap (baseJ.restrict V) := by
          rw [htarget_eq]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The localized patch proof replays the global reverse-domination handoff plus the
-- patch-parametric raw-order COV, which is heartbeat-heavy after unfolding the
-- Case 2 with-following coordinate families.
/-- Localized reverse determinant-Haar to raw-Haar domination for the
with-following Case 2 source measure.

This is the patch-parametric form of
`exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple`:
instead of assuming domination on the whole determinant chart and concluding
on the whole raw-order source chart, it assumes domination on
`rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P` and concludes on the raw-order patch
`P`.

The endpoint-patch reverse domination hypothesis remains explicit.  This
theorem uses the retained-passive formal-product Jacobian COV; it does not
prove source-prior transport, exact raw-Haar pushforward, raw-Haar
normalization, source-image/source-rank coverage, normal crossings, pole order,
or RLCT extraction. -/
theorem exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple
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
    (sourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
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
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      sourceMeasure.withDensity jacobianDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
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
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        AEMeasurable rawMap (baseJ.restrict V) ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure]
          {P : Set RawTuple} {c : ℝ≥0∞},
          P ⊆ rawSourceSet →
            NullMeasurableSet (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) rawHaar →
              rawHaar.restrict (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) ≤
                  c • Measure.map Y (sourceMeasure.restrict V) →
                rawHaar.restrict P ≤
                  c • Measure.map rawMap (baseJ.restrict V) := by
  intro RawTuple Y jacobianDensity baseJ rawMap rawOrderOnEndpoint rawDetChart
    rawSourceSet
  rcases
      exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hpoint, _hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_, ?_⟩
  · let ρ := Fin (Module.finrank ℝ U₀)
    let κ' : Fin 3 → Type :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    have hdet_of_mem :
        ∀ z ∈ V,
          Y z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
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
              case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
                (ρ := ρ) n hS hcont hnext z.1 eNext e)
          exact
            (continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
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
    exact
      ContinuousOn.aemeasurable₀ hrawMapContOn
        hVopen.measurableSet.nullMeasurableSet
  intro rawHaar _instRawHaar P c hP hendpoint_nm hYdom
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let Φ : RawTuple → RawTuple :=
    fun y ↦
      topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
  let endpointPatch : Set RawTuple := rawDetChart ∩ Φ ⁻¹' P
  let formalDensity : RawTuple → ℝ≥0∞ :=
    fun y ↦
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := 1) (ρ := ρ) (κ' := κ') y)
  have hY :
      AEMeasurable Y (sourceMeasure.restrict V) := by
    have hYcont : Continuous Y := by
      simpa [Y, RawTuple, ρ, κ'] using
        continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hdet_meas : MeasurableSet rawDetChart := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hY_mem :
      ∀ᵐ z ∂sourceMeasure.restrict V, Y z ∈ rawDetChart := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    simpa [Y, rawDetChart, RawTuple, ρ, κ'] using (hpoint z hz).1
  have hmapY_mem :
      ∀ᵐ y ∂Measure.map Y (sourceMeasure.restrict V),
        y ∈ rawDetChart :=
    (ae_map_iff hY hdet_meas).2 hY_mem
  have hmapY_restrict :
      (Measure.map Y (sourceMeasure.restrict V)).restrict rawDetChart =
        Measure.map Y (sourceMeasure.restrict V) :=
    Measure.restrict_eq_self_of_ae_mem hmapY_mem
  have hdet_nm_mapY :
      NullMeasurableSet rawDetChart (Measure.map Y (sourceMeasure.restrict V)) :=
    hdet_meas.nullMeasurableSet
  have hformalDensity_map_restrict :
      AEMeasurable formalDensity
        ((Measure.map Y (sourceMeasure.restrict V)).restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm_mapY
    intro y hy
    exact
      (ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_of_mem_topologyTupleDetChartSet
          (M := 1) (ρ := ρ) (κ' := κ') y (by
            simpa [rawDetChart, RawTuple, ρ, κ'] using hy))).continuousWithinAt
  have hformalDensity_map :
      AEMeasurable formalDensity
        (Measure.map Y (sourceMeasure.restrict V)) := by
    simpa [hmapY_restrict] using hformalDensity_map_restrict
  have hΦ_map_restrict :
      AEMeasurable Φ
        ((Measure.map Y (sourceMeasure.restrict V)).restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm_mapY
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ_map :
      AEMeasurable Φ (Measure.map Y (sourceMeasure.restrict V)) := by
    simpa [hmapY_restrict] using hΦ_map_restrict
  have hΦ_map_weighted :
      AEMeasurable Φ
        ((Measure.map Y (sourceMeasure.restrict V)).withDensity
          formalDensity) :=
    hΦ_map.mono_ac (withDensity_absolutelyContinuous _ _)
  have hΦ_ref_map :
      Measure.map Φ ((rawHaar.restrict endpointPatch).withDensity formalDensity) =
        rawHaar.restrict P := by
    simpa [Φ, formalDensity, endpointPatch, rawDetChart, rawSourceSet,
      rawOrderOnEndpoint, RawTuple, ρ, κ'] using
      map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_patch_of_subset_rawSource
        (M := 1) (ρ := ρ) (κ' := κ') rawHaar hendpoint_nm hP
  have hbase_restrict :
      baseJ.restrict V =
        (sourceMeasure.restrict V).withDensity (fun z ↦ formalDensity (Y z)) := by
    change (sourceMeasure.withDensity jacobianDensity).restrict V =
      (sourceMeasure.restrict V).withDensity (fun z ↦ formalDensity (Y z))
    rw [restrict_withDensity hVopen.measurableSet]
  have hweighted :
      rawHaar.restrict P ≤
        c • Measure.map (fun z ↦ Φ (Y z))
          ((sourceMeasure.restrict V).withDensity
            (fun z ↦ formalDensity (Y z))) :=
    DLNFibre.DLN.Aoyagi.weighted_map_ref_le_smul_map_comp_withDensity_comp_of_le_smul_map
      (μ := sourceMeasure.restrict V)
      (sourceRef := rawHaar.restrict endpointPatch)
      (targetRef := rawHaar.restrict P)
      (pre := Y) (post := Φ) (density := formalDensity)
      hY hformalDensity_map hΦ_map_weighted hYdom hΦ_ref_map
  have htarget_eq :
      Measure.map (fun z ↦ Φ (Y z))
          ((sourceMeasure.restrict V).withDensity
            (fun z ↦ formalDensity (Y z))) =
        Measure.map rawMap (baseJ.restrict V) := by
    rw [hbase_restrict]
  calc
    rawHaar.restrict P ≤
        c • Measure.map (fun z ↦ Φ (Y z))
          ((sourceMeasure.restrict V).withDensity
            (fun z ↦ formalDensity (Y z))) := hweighted
    _ = c • Measure.map rawMap (baseJ.restrict V) := by
          rw [htarget_eq]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete coordinate-source stack has long dependent `let`s, but the proof is the generic handoff.
/-- Conditional domination for the concrete with-following coordinate source measure.

This is the concrete Aoyagi wrapper around the generic two-density handoff:
`referenceSource` is first weighted by the retained-passive raw-order Jacobian
density, and the result is then weighted by the endpoint source-image density.
The base domination of `referenceSource.restrict V` and the two local density
bounds remain explicit hypotheses. -/
theorem case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_restrict_le_smul_of_referenceSource_restrict_le_smul
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (ν :
      Measure
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    {Cbase CJ CS : ℝ≥0∞}
    (hV : MeasurableSet V) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    referenceSource.restrict V ≤ Cbase • ν →
      (∀ᵐ z ∂referenceSource.restrict V, jacobianDensity z ≤ CJ) →
        (∀ᵐ z ∂baseJ.restrict V, sourceDensity z ≤ CS) →
          coordinateSourceMeasure.restrict V ≤
            (CS * (CJ * Cbase)) • ν := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily sourceChart
    sourceDensity coordinateSourceMeasure hbase hJ hsource
  simpa [baseJ, coordinateSourceMeasure] using
    restrict_two_withDensity_le_smul_of_restrict_le_smul_of_ae_le
      (μ := referenceSource) (ν := ν) (J := jacobianDensity) (S := sourceDensity)
      hV hbase hJ hsource

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Same concrete stack, with the finite scalar fact bundled for downstream dominated-target use.
/-- Finite-scalar version of
`case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_restrict_le_smul_of_referenceSource_restrict_le_smul`. -/
theorem case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_restrict_le_smul_of_referenceSource_restrict_le_smul_of_lt_top
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (ν :
      Measure
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    {Cbase CJ CS : ℝ≥0∞}
    (hV : MeasurableSet V) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    referenceSource.restrict V ≤ Cbase • ν →
      (∀ᵐ z ∂referenceSource.restrict V, jacobianDensity z ≤ CJ) →
        (∀ᵐ z ∂baseJ.restrict V, sourceDensity z ≤ CS) →
          Cbase < ∞ →
            CJ < ∞ →
              CS < ∞ →
                (CS * (CJ * Cbase)) < ∞ ∧
                  coordinateSourceMeasure.restrict V ≤
                    (CS * (CJ * Cbase)) • ν := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily sourceChart
    sourceDensity coordinateSourceMeasure hbase hJ hsource hCbase hCJ hCS
  simpa [baseJ, coordinateSourceMeasure] using
    restrict_two_withDensity_le_smul_of_restrict_le_smul_of_ae_le_of_lt_top
      (μ := referenceSource) (ν := ν) (J := jacobianDensity) (S := sourceDensity)
      hV hbase hJ hsource hCbase hCJ hCS

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Composes the fixed-patch finite-source theorem with two density handoffs.
/-- Fixed-following-patch finite-integral handoff for the concrete
with-following coordinate source measure.

Unlike the existential handoffs below, this theorem consumes an already chosen
following patch with finite matrix-entry measure and determinant/inverse-bound
data.  This is the right API when a later source-chart shrink has to use the
same following patch that supplies finite integrability. -/
theorem case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_restrict_of_followingPatch_passive_restrict_le_smul_and_density_bounds
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
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    {t K : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (followingPatch :
      Set (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ))
    (hpatch_meas : MeasurableSet followingPatch)
    (hpatch_lt_top :
      matrixEntryReferenceMeasure
        (Case2ResidualColIndex n S (J + 1)) τ followingPatch < ∞)
    (hpatch_det :
      ∀ F ∈ followingPatch, IsUnit ((F.submatrix id eNext.symm).det))
    (hpatch_inv_bound :
      ∀ F ∈ followingPatch,
        aoyagiCoordinateSquareSum
            (fun ij : τ × Case2ResidualColIndex n S (J + 1) =>
              (((F.submatrix id eNext.symm)⁻¹).submatrix eNext id)
                ij.1 ij.2) ≤ K)
    (passiveLocalSet :
      Set
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    {Cpassive CJ CS : ℝ≥0∞}
    (hV : MeasurableSet V)
    (hpassive :
      (case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J).restrict
          passiveLocalSet ≤ Cpassive • passiveMeasure)
    (hV_passive :
      V ⊆
        {z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
          z.1.1 ∈ passiveLocalSet})
    (hV_following :
      V ⊆
        {z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
          z.2 ∈ followingPatch})
    (hCpassive : Cpassive < ∞)
    (hCJ : CJ < ∞)
    (hCS : CS < ∞) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    (∀ᵐ z ∂referenceSource.restrict V, jacobianDensity z ≤ CJ) →
      (∀ᵐ z ∂baseJ.restrict V, sourceDensity z ≤ CS) →
        let productResidual :
            Case2PassiveThetaWithFollowingFactor
                (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
              Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
          fun z ij ↦
            (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
              (ChartLocalSuffixState.residualFactorProduct
                (case2PassiveThetaWithFollowingFactorEndpointRetainedData
                  (ρ := Fin (Module.finrank ℝ U₀))
                  n hS hcont hnext z eNext e).C
                (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
                  (e (Fin.last 2)) (e 0)) ij.1 ij.2
        (∀ᵐ z ∂ coordinateSourceMeasure.restrict V,
          0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
          (∫⁻ z :
              Case2PassiveThetaWithFollowingFactor
                (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J,
            ENNReal.ofReal
              ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
              ∂ coordinateSourceMeasure.restrict V) < ∞ := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily sourceChart
    sourceDensity coordinateSourceMeasure hJ hsource productResidual
  classical
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  haveI : IsFiniteMeasure passiveMeasure := ⟨hpassive_lt_top⟩
  let center : Finset (ℕ × ℕ) :=
    case2ResidualBlockPivotEntries n S (J + 1)
  let pivotNext : center :=
    case2PassiveThetaPivotNext n hS hnext
  let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
    Measure.pi
      (fun i : Case2PassiveTheta.Center n S J =>
        volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
  let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
    signedBox.withDensity
      (fun y : Case2PassiveTheta.Center n S J → ℝ =>
        ENNReal.ofReal
          (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
  let followingMeasure :=
    matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
  let sourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    ((passiveMeasure.prod weightedBox).prod followingMeasure).restrict
      {z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J |
        z.2 ∈ followingPatch}
  let localSourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    sourceMeasure.restrict V
  have hfinite_prod :
      let center : Finset (ℕ × ℕ) :=
        case2ResidualBlockPivotEntries n S (J + 1)
      let pivotNext : center :=
        case2PassiveThetaPivotNext n hS hnext
      let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
        Measure.pi
          (fun i : Case2PassiveTheta.Center n S J =>
            volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
      let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
        signedBox.withDensity
          (fun y : Case2PassiveTheta.Center n S J → ℝ =>
            ENNReal.ofReal
              (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let sourceMeasure :
          Measure
            (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
        (passiveMeasure.prod weightedBox).prod
          ((matrixEntryReferenceMeasure
            (Case2ResidualColIndex n S (J + 1)) τ).restrict followingPatch)
      let productResidual :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
            Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
        fun z ij ↦
          (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
            (ChartLocalSuffixState.residualFactorProduct
              (case2PassiveThetaWithFollowingFactorEndpointRetainedData
                (ρ := ρ) n hS hcont hnext z eNext e).C
              (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
                (e (Fin.last 2)) (e 0)) ij.1 ij.2
      (∀ᵐ z ∂ sourceMeasure, 0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
        (∫⁻ z :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
            ∂ sourceMeasure) < ∞ := by
    haveI :
        SFinite
          (matrixEntryReferenceMeasure
            (Case2ResidualColIndex n S (J + 1)) τ) :=
      sFinite_matrixEntryReferenceMeasure
        (Case2ResidualColIndex n S (J + 1)) τ
    exact
      case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_restrict_followingPatch_of_forall_mem_reindexed_det_isUnit_inverse_squareSum_le
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext
        passiveMeasure hpassive_lt_top
        (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)
        hpatch_meas hpatch_lt_top (t := t) (K := K) Rres ht hRres hcrit
        eNext e hpatch_det hpatch_inv_bound
  have hfinite_source :
      let center : Finset (ℕ × ℕ) :=
        case2ResidualBlockPivotEntries n S (J + 1)
      let pivotNext : center :=
        case2PassiveThetaPivotNext n hS hnext
      let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
        Measure.pi
          (fun i : Case2PassiveTheta.Center n S J =>
            volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
      let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
        signedBox.withDensity
          (fun y : Case2PassiveTheta.Center n S J → ℝ =>
            ENNReal.ofReal
              (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let followingMeasure :=
        matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
      let sourceMeasure :
          Measure
            (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
        ((passiveMeasure.prod weightedBox).prod followingMeasure).restrict
          {z :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J |
            z.2 ∈ followingPatch}
      let productResidual :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
            Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
        fun z ij ↦
          (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
            (ChartLocalSuffixState.residualFactorProduct
              (case2PassiveThetaWithFollowingFactorEndpointRetainedData
                (ρ := ρ) n hS hcont hnext z eNext e).C
              (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
                (e (Fin.last 2)) (e 0)) ij.1 ij.2
      (∀ᵐ z ∂ sourceMeasure, 0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
        (∫⁻ z :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
            ∂ sourceMeasure) < ∞ := by
    simpa [
      case2PassiveThetaWithFollowingFactor_productSourceMeasure_restrict_followingPatch_eq_prod_restrict
        (ρ := ρ) (τ := τ) n hS hnext passiveMeasure Rres followingPatch
    ] using hfinite_prod
  have hfinite_local :
      let center : Finset (ℕ × ℕ) :=
        case2ResidualBlockPivotEntries n S (J + 1)
      let pivotNext : center :=
        case2PassiveThetaPivotNext n hS hnext
      let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
        Measure.pi
          (fun i : Case2PassiveTheta.Center n S J =>
            volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
      let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
        signedBox.withDensity
          (fun y : Case2PassiveTheta.Center n S J → ℝ =>
            ENNReal.ofReal
              (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let followingMeasure :=
        matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
      let sourceMeasure :
          Measure
            (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
        ((passiveMeasure.prod weightedBox).prod followingMeasure).restrict
          {z :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J |
            z.2 ∈ followingPatch}
      let localSourceMeasure :
          Measure
            (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
        sourceMeasure.restrict V
      let productResidual :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
            Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
        fun z ij ↦
          (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
            (ChartLocalSuffixState.residualFactorProduct
              (case2PassiveThetaWithFollowingFactorEndpointRetainedData
                (ρ := ρ) n hS hcont hnext z eNext e).C
              (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
                (e (Fin.last 2)) (e 0)) ij.1 ij.2
      (∀ᵐ z ∂ localSourceMeasure, 0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
        (∫⁻ z :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
            ∂ localSourceMeasure) < ∞ := by
    exact
      ⟨ae_restrict_of_ae hfinite_source.1,
        lt_of_le_of_lt
          (lintegral_mono' Measure.restrict_le_self (le_refl _))
          hfinite_source.2⟩
  have hbase :
      referenceSource.restrict V ≤ Cpassive • localSourceMeasure := by
    simpa [ρ, referenceSource, localSourceMeasure, sourceMeasure,
      followingMeasure, weightedBox, signedBox] using
      case2PassiveThetaWithFollowingFactor_referenceSource_restrict_le_smul_sourceCylinder_restrict_of_passive_restrict_le_smul
        (ρ := ρ) (τ := τ) n hS hnext passiveMeasure Rres
        passiveLocalSet followingPatch V hpassive hV_passive hV_following
  have hcoordinate :
      (CS * (CJ * Cpassive)) < ∞ ∧
        coordinateSourceMeasure.restrict V ≤
          (CS * (CJ * Cpassive)) • localSourceMeasure := by
    simpa [RawTuple, Y, referenceSource, jacobianDensity, baseJ, EdgeFamily,
      sourceChart, sourceDensity, coordinateSourceMeasure, localSourceMeasure] using
      case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_restrict_le_smul_of_referenceSource_restrict_le_smul_of_lt_top
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e sourceImageDensity Rres V localSourceMeasure
        (Cbase := Cpassive) (CJ := CJ) (CS := CS)
        hV hbase hJ hsource hCpassive hCJ hCS
  simpa [ρ, κ', productResidual] using
    ae_and_lintegral_lt_top_of_measure_le_smul hcoordinate.2 hcoordinate.1
      hfinite_local.1 hfinite_local.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- First constructs the finite open patch, then shrinks the same source chart into it.
/-- Open-patch and open-source-neighborhood finite-integral handoff for the
concrete with-following coordinate source measure.

The theorem removes the old continuation `V ⊆ {z | z.2 ∈ followingPatch}` by
choosing the open following patch first and then shrinking the source-chart
neighborhood inside its cylinder.  Passive comparison and the two density
upper bounds remain explicit hypotheses/continuations. -/
theorem exists_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds
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
    (hDomainOpens :
      OpensMeasurableSpace
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hDomainBorel :
      BorelSpace
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hDomainPolish :
      PolishSpace
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
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
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (passiveLocalSet :
      Set
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    {Cpassive CJ CS : ℝ≥0∞}
    (hpassive :
      (case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J).restrict
          passiveLocalSet ≤ Cpassive • passiveMeasure)
    (hCpassive : Cpassive < ∞)
    (hCJ : CJ < ∞)
    (hCS : CS < ∞)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G)
    (hG_passive :
      G ⊆
        {z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
          z.1.1 ∈ passiveLocalSet}) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let retainedData :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    ∃ followingPatch :
        Set (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ), ∃ K : ℝ,
      ∃ V :
        Set
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      0 < K ∧
        z₀.2 ∈ followingPatch ∧
        IsOpen followingPatch ∧
        MeasurableSet followingPatch ∧
        matrixEntryReferenceMeasure
          (Case2ResidualColIndex n S (J + 1)) τ followingPatch < ∞ ∧
        (∀ F ∈ followingPatch, IsUnit ((F.submatrix id eNext.symm).det)) ∧
        (∀ F ∈ followingPatch,
          aoyagiCoordinateSquareSum
              (fun ij : τ × Case2ResidualColIndex n S (J + 1) =>
                (((F.submatrix id eNext.symm)⁻¹).submatrix eNext id)
                  ij.1 ij.2) ≤ K) ∧
        IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        V ⊆
          {z :
            Case2PassiveThetaWithFollowingFactor
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
            z.1.1 ∈ passiveLocalSet} ∧
        V ⊆
          {z :
            Case2PassiveThetaWithFollowingFactor
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
            z.2 ∈ followingPatch} ∧
        (∀ z ∈ V, (retainedData z).detChart) ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
        Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
        MeasurableSet (sourceChart '' V) ∧
        ((∀ᵐ z ∂referenceSource.restrict V, jacobianDensity z ≤ CJ) →
          (∀ᵐ z ∂baseJ.restrict V, sourceDensity z ≤ CS) →
            let productResidual :
                Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
                  Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
              fun z ij ↦
                (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
                  (ChartLocalSuffixState.residualFactorProduct
                    (case2PassiveThetaWithFollowingFactorEndpointRetainedData
                      (ρ := Fin (Module.finrank ℝ U₀))
                      n hS hcont hnext z eNext e).C
                    (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
                      (e (Fin.last 2)) (e 0)) ij.1 ij.2
            (∀ᵐ z ∂ coordinateSourceMeasure.restrict V,
              0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
              (∫⁻ z :
                  Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J,
                ENNReal.ofReal
                  ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
                  ∂ coordinateSourceMeasure.restrict V) < ∞) := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily sourceChart
    sourceDensity coordinateSourceMeasure retainedData readback
  classical
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let SourceDomain :=
    Case2PassiveThetaWithFollowingFactor
      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
  letI : OpensMeasurableSpace SourceDomain := hDomainOpens
  letI : BorelSpace SourceDomain := hDomainBorel
  letI : PolishSpace SourceDomain := hDomainPolish
  rcases
      exists_matrixEntryReferenceMeasure_finite_open_followingPatch_of_reindexed_det_isUnit
        eNext z₀.2 hF₀det with
    ⟨followingPatch, K, hK_pos, hz₀_following, hpatch_open, hpatch_meas,
      hpatch_lt_top, hpatch_det, hpatch_inv_bound⟩
  rcases
      (by
        simpa [EdgeFamily, retainedData, sourceChart, readback] using
          _root_.DLNFibre.DLN.Aoyagi.exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse_subset_followingPatchCylinder
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
            eNext e z₀ hdet₀ hpivot₀ followingPatch hpatch_open
            hz₀_following G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hV_following, hdetV, hleftV, hsource_inj,
      hsource_contOn, hsource_image⟩
  have hV_passive :
      V ⊆
        {z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
          z.1.1 ∈ passiveLocalSet} := fun z hz ↦ hG_passive (hVG hz)
  have hdetV' : ∀ z ∈ V, (retainedData z).detChart := by
    simpa [retainedData] using hdetV
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    simpa [sourceChart, readback] using hleftV
  refine
    ⟨followingPatch, K, V, hK_pos, hz₀_following, hpatch_open, hpatch_meas,
      hpatch_lt_top, hpatch_det, hpatch_inv_bound, hVopen, hz₀V, hVG,
      hV_passive, hV_following, hdetV', hleftV', hsource_inj, hsource_contOn,
      hsource_image, ?_⟩
  intro hJ hsource productResidual
  have hfinite :=
    case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_restrict_of_followingPatch_passive_restrict_le_smul_and_density_bounds
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
      eNext e passiveMeasure hpassive_lt_top sourceImageDensity
      (t := t) (K := K) Rres ht hRres hcrit
      followingPatch hpatch_meas hpatch_lt_top hpatch_det hpatch_inv_bound
      passiveLocalSet V hVopen.measurableSet hpassive hV_passive hV_following
      hCpassive hCJ hCS hJ hsource
  simpa [RawTuple, Y, referenceSource, jacobianDensity, baseJ, EdgeFamily,
    sourceChart, sourceDensity, coordinateSourceMeasure, productResidual, ρ, κ'] using
    hfinite

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Chooses the passive self-restriction, then calls the supplied-passive open-patch wrapper.
/-- Open-patch coordinate-source finite-integral handoff with the passive
coordinate-reference self-restriction constructed internally.

This removes the supplied passive-local comparison hypothesis from
`exists_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds`.
The remaining continuations are exactly the two genuine density upper bounds
on the returned local set `V`. -/
theorem exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_density_bounds
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
    (hDomainOpens :
      OpensMeasurableSpace
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hDomainBorel :
      BorelSpace
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hDomainPolish :
      PolishSpace
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
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
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {CJ CS : ℝ≥0∞}
    (hCJ : CJ < ∞)
    (hCS : CS < ∞)
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
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let retainedData :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let passiveRef :=
      case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    ∃ passiveLocalSet :
        Set
          (Case2PassiveTheta.PassiveFields
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      ∃ passiveMeasure :
        Measure
          (Case2PassiveTheta.PassiveFields
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      ∃ followingPatch :
        Set (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ), ∃ K : ℝ,
      ∃ V :
        Set
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      z₀.1.1 ∈ passiveLocalSet ∧
        IsOpen passiveLocalSet ∧
        MeasurableSet passiveLocalSet ∧
        passiveMeasure = passiveRef.restrict passiveLocalSet ∧
        passiveMeasure Set.univ < ∞ ∧
        passiveRef.restrict passiveLocalSet ≤ (1 : ℝ≥0∞) • passiveMeasure ∧
        0 < K ∧
        z₀.2 ∈ followingPatch ∧
        IsOpen followingPatch ∧
        MeasurableSet followingPatch ∧
        matrixEntryReferenceMeasure
          (Case2ResidualColIndex n S (J + 1)) τ followingPatch < ∞ ∧
        (∀ F ∈ followingPatch, IsUnit ((F.submatrix id eNext.symm).det)) ∧
        (∀ F ∈ followingPatch,
          aoyagiCoordinateSquareSum
              (fun ij : τ × Case2ResidualColIndex n S (J + 1) =>
                (((F.submatrix id eNext.symm)⁻¹).submatrix eNext id)
                  ij.1 ij.2) ≤ K) ∧
        IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        V ⊆
          {z :
            Case2PassiveThetaWithFollowingFactor
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
            z.1.1 ∈ passiveLocalSet} ∧
        V ⊆
          {z :
            Case2PassiveThetaWithFollowingFactor
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
            z.2 ∈ followingPatch} ∧
        (∀ z ∈ V, (retainedData z).detChart) ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
        Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
        MeasurableSet (sourceChart '' V) ∧
        ((∀ᵐ z ∂referenceSource.restrict V, jacobianDensity z ≤ CJ) →
          (∀ᵐ z ∂baseJ.restrict V, sourceDensity z ≤ CS) →
            let productResidual :
                Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
                  Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
              fun z ij ↦
                (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
                  (ChartLocalSuffixState.residualFactorProduct
                    (case2PassiveThetaWithFollowingFactorEndpointRetainedData
                      (ρ := Fin (Module.finrank ℝ U₀))
                      n hS hcont hnext z eNext e).C
                    (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
                      (e (Fin.last 2)) (e 0)) ij.1 ij.2
            (∀ᵐ z ∂ coordinateSourceMeasure.restrict V,
              0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
              (∫⁻ z :
                  Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J,
                ENNReal.ofReal
                  ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
                  ∂ coordinateSourceMeasure.restrict V) < ∞) := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily sourceChart
    sourceDensity coordinateSourceMeasure retainedData readback passiveRef
  classical
  let ρ := Fin (Module.finrank ℝ U₀)
  let SourceDomain :=
    Case2PassiveThetaWithFollowingFactor
      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
  letI : OpensMeasurableSpace SourceDomain := hDomainOpens
  letI : BorelSpace SourceDomain := hDomainBorel
  letI : PolishSpace SourceDomain := hDomainPolish
  rcases
      _root_.DLNFibre.DLN.Aoyagi.exists_open_passiveLocalSet_case2PassiveThetaPassiveFieldReferenceMeasure_restrict_self_le_smul
        (ρ := ρ) (τ := τ) n S J z₀.1.1 with
    ⟨passiveLocalSet, passiveMeasure, Cpassive, hz₀_passive, hpassive_open,
      hpassive_meas, hpassive_eq, hpassive_lt_top, hCpassive_eq,
      hCpassive_lt, hpassive_dom⟩
  let passiveCylinder : Set SourceDomain :=
    {z : SourceDomain | z.1.1 ∈ passiveLocalSet}
  let Gpassive : Set SourceDomain := G ∩ passiveCylinder
  have hpassiveCylinder_open : IsOpen passiveCylinder := by
    simpa [passiveCylinder, SourceDomain] using
      _root_.DLNFibre.DLN.Aoyagi.isOpen_case2PassiveThetaWithFollowingFactor_passiveFieldCylinder
        (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J) hpassive_open
  have hGpassive_open : IsOpen Gpassive := hGopen.inter hpassiveCylinder_open
  have hz₀Gpassive : z₀ ∈ Gpassive := by
    exact ⟨hz₀G, hz₀_passive⟩
  have hGpassive_passive :
      Gpassive ⊆
        {z : SourceDomain | z.1.1 ∈ passiveLocalSet} := by
    intro z hz
    exact hz.2
  rcases
      exists_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        hDomainOpens hDomainBorel hDomainPolish eNext e z₀ hdet₀ hpivot₀
        hF₀det passiveMeasure hpassive_lt_top sourceImageDensity
        (t := t) Rres ht hRres hcrit passiveLocalSet
        (Cpassive := Cpassive) (CJ := CJ) (CS := CS)
        hpassive_dom hCpassive_lt hCJ hCS Gpassive hGpassive_open
        hz₀Gpassive hGpassive_passive with
    ⟨followingPatch, K, V, hK_pos, hz₀_following, hpatch_open, hpatch_meas,
      hpatch_lt_top, hpatch_det, hpatch_inv_bound, hVopen, hz₀V,
      hVGpassive, hV_passive, hV_following, hdetV, hleftV, hsource_inj,
      hsource_contOn, hsource_image, hfinite⟩
  have hVG : V ⊆ G := fun z hz ↦ (hVGpassive hz).1
  have hpassive_dom_one :
      passiveRef.restrict passiveLocalSet ≤ (1 : ℝ≥0∞) • passiveMeasure := by
    simpa [passiveRef, hCpassive_eq] using hpassive_dom
  refine
    ⟨passiveLocalSet, passiveMeasure, followingPatch, K, V, hz₀_passive,
      hpassive_open, hpassive_meas, ?_, hpassive_lt_top, hpassive_dom_one,
      hK_pos, hz₀_following, hpatch_open, hpatch_meas, hpatch_lt_top,
      hpatch_det, hpatch_inv_bound, hVopen, hz₀V, hVG, hV_passive,
      hV_following, hdetV, hleftV, hsource_inj, hsource_contOn,
      hsource_image, ?_⟩
  · simpa [passiveRef] using hpassive_eq
  · intro hJ hsource productResidual
    simpa [RawTuple, Y, referenceSource, jacobianDensity, baseJ, EdgeFamily,
      sourceChart, sourceDensity, coordinateSourceMeasure, productResidual] using
      hfinite hJ hsource

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The statement unfolds the concrete coordinate-source stack and composes three long handoff theorems.
/-- Conditional finite-integral handoff for the concrete with-following
coordinate source measure.

The finite following-patch source theorem first constructs the following patch.
If the local set `V` is then known to lie in that following-patch cylinder,
passive local domination and the two local upper-density bounds dominate the
coordinate source by the finite source cylinder.  The dominated-target theorem
then transfers p.13 product-residual a.e. positivity and finite negative-power
integrability to `coordinateSourceMeasure.restrict V`.

This theorem does not construct the passive comparison measure or prove the
Jacobian/source-density upper bounds. -/
theorem exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds
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
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (passiveLocalSet :
      Set
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    {Cpassive CJ CS : ℝ≥0∞}
    (hV : MeasurableSet V)
    (hpassive :
      (case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J).restrict
          passiveLocalSet ≤ Cpassive • passiveMeasure)
    (hV_passive :
      V ⊆
        {z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
          z.1.1 ∈ passiveLocalSet})
    (hCpassive : Cpassive < ∞)
    (hCJ : CJ < ∞)
    (hCS : CS < ∞)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det)) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    (∀ᵐ z ∂referenceSource.restrict V, jacobianDensity z ≤ CJ) →
      (∀ᵐ z ∂baseJ.restrict V, sourceDensity z ≤ CS) →
        ∃ followingPatch :
            Set (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ), ∃ K : ℝ,
          0 < K ∧
            z₀.2 ∈ followingPatch ∧
            MeasurableSet followingPatch ∧
            matrixEntryReferenceMeasure
              (Case2ResidualColIndex n S (J + 1)) τ followingPatch < ∞ ∧
            (∀ F ∈ followingPatch, IsUnit ((F.submatrix id eNext.symm).det)) ∧
            (∀ F ∈ followingPatch,
              aoyagiCoordinateSquareSum
                  (fun ij : τ × Case2ResidualColIndex n S (J + 1) =>
                    (((F.submatrix id eNext.symm)⁻¹).submatrix eNext id)
                      ij.1 ij.2) ≤ K) ∧
            let productResidual :
                Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
                  Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
              fun z ij ↦
                (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
                  (ChartLocalSuffixState.residualFactorProduct
                    (case2PassiveThetaWithFollowingFactorEndpointRetainedData
                      (ρ := Fin (Module.finrank ℝ U₀))
                      n hS hcont hnext z eNext e).C
                    (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
                      (e (Fin.last 2)) (e 0)) ij.1 ij.2
            V ⊆
                {z :
                  Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
                  z.2 ∈ followingPatch} →
              (∀ᵐ z ∂ coordinateSourceMeasure.restrict V,
                0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
                (∫⁻ z :
                    Case2PassiveThetaWithFollowingFactor
                      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J,
                  ENNReal.ofReal
                    ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
                    ∂ coordinateSourceMeasure.restrict V) < ∞ := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily sourceChart
    sourceDensity coordinateSourceMeasure hJ hsource
  classical
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  haveI : IsFiniteMeasure passiveMeasure := ⟨hpassive_lt_top⟩
  rcases
      exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_of_measure_le_smul_restrict_sourceCylinder_restrict_of_base_reindexed_det_isUnit
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext
        passiveMeasure hpassive_lt_top (t := t) Rres ht hRres hcrit
        eNext e z₀ V hF₀det with
    ⟨followingPatch, K, hK_pos, hF₀_mem, hpatch_meas, hpatch_lt_top,
      hpatch_det, hpatch_inv_bound, hfinite_target⟩
  refine
    ⟨followingPatch, K, hK_pos, hF₀_mem, hpatch_meas, hpatch_lt_top,
      hpatch_det, hpatch_inv_bound, ?_⟩
  intro productResidual hV_following
  let center : Finset (ℕ × ℕ) :=
    case2ResidualBlockPivotEntries n S (J + 1)
  let pivotNext : center :=
    case2PassiveThetaPivotNext n hS hnext
  let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
    Measure.pi
      (fun i : Case2PassiveTheta.Center n S J =>
        volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
  let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
    signedBox.withDensity
      (fun y : Case2PassiveTheta.Center n S J → ℝ =>
        ENNReal.ofReal
          (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
  let followingMeasure :=
    matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
  let sourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    ((passiveMeasure.prod weightedBox).prod followingMeasure).restrict
      {z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J |
        z.2 ∈ followingPatch}
  let localSourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    sourceMeasure.restrict V
  have hbase :
      referenceSource.restrict V ≤ Cpassive • localSourceMeasure := by
    simpa [ρ, referenceSource, localSourceMeasure, sourceMeasure,
      followingMeasure, weightedBox, signedBox] using
      case2PassiveThetaWithFollowingFactor_referenceSource_restrict_le_smul_sourceCylinder_restrict_of_passive_restrict_le_smul
        (ρ := ρ) (τ := τ) n hS hnext passiveMeasure Rres
        passiveLocalSet followingPatch V hpassive hV_passive hV_following
  have hcoordinate :
      (CS * (CJ * Cpassive)) < ∞ ∧
        coordinateSourceMeasure.restrict V ≤
          (CS * (CJ * Cpassive)) • localSourceMeasure := by
    simpa [RawTuple, Y, referenceSource, jacobianDensity, baseJ, EdgeFamily,
      sourceChart, sourceDensity, coordinateSourceMeasure, localSourceMeasure] using
      case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_restrict_le_smul_of_referenceSource_restrict_le_smul_of_lt_top
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e sourceImageDensity Rres V localSourceMeasure
        (Cbase := Cpassive) (CJ := CJ) (CS := CS)
        hV hbase hJ hsource hCpassive hCJ hCS
  simpa [ρ, κ', productResidual] using
    hfinite_target.2 (coordinateSourceMeasure.restrict V)
      (CS * (CJ * Cpassive)) hcoordinate.2 hcoordinate.1

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The statement preserves the open following-patch witness for later source-chart shrinking.
/-- Open-patch finite-integral handoff for the concrete with-following
coordinate source measure.

This is the open-witness version of
`exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds`.
The returned following patch is open, so later source-chart arguments can
shrink into the following-patch cylinder. -/
theorem exists_matrixEntryReference_open_followingPatch_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_passive_restrict_le_smul_and_density_bounds
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
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (passiveLocalSet :
      Set
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    {Cpassive CJ CS : ℝ≥0∞}
    (hV : MeasurableSet V)
    (hpassive :
      (case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J).restrict
          passiveLocalSet ≤ Cpassive • passiveMeasure)
    (hV_passive :
      V ⊆
        {z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
          z.1.1 ∈ passiveLocalSet})
    (hCpassive : Cpassive < ∞)
    (hCJ : CJ < ∞)
    (hCS : CS < ∞)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det)) :
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    (∀ᵐ z ∂referenceSource.restrict V, jacobianDensity z ≤ CJ) →
      (∀ᵐ z ∂baseJ.restrict V, sourceDensity z ≤ CS) →
        ∃ followingPatch :
            Set (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ), ∃ K : ℝ,
          0 < K ∧
            z₀.2 ∈ followingPatch ∧
            IsOpen followingPatch ∧
            MeasurableSet followingPatch ∧
            matrixEntryReferenceMeasure
              (Case2ResidualColIndex n S (J + 1)) τ followingPatch < ∞ ∧
            (∀ F ∈ followingPatch, IsUnit ((F.submatrix id eNext.symm).det)) ∧
            (∀ F ∈ followingPatch,
              aoyagiCoordinateSquareSum
                  (fun ij : τ × Case2ResidualColIndex n S (J + 1) =>
                    (((F.submatrix id eNext.symm)⁻¹).submatrix eNext id)
                      ij.1 ij.2) ≤ K) ∧
            let productResidual :
                Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
                  Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
              fun z ij ↦
                (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
                  (ChartLocalSuffixState.residualFactorProduct
                    (case2PassiveThetaWithFollowingFactorEndpointRetainedData
                      (ρ := Fin (Module.finrank ℝ U₀))
                      n hS hcont hnext z eNext e).C
                    (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
                      (e (Fin.last 2)) (e 0)) ij.1 ij.2
            V ⊆
                {z :
                  Case2PassiveThetaWithFollowingFactor
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J |
                  z.2 ∈ followingPatch} →
              (∀ᵐ z ∂ coordinateSourceMeasure.restrict V,
                0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
                (∫⁻ z :
                    Case2PassiveThetaWithFollowingFactor
                      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J,
                  ENNReal.ofReal
                    ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
                    ∂ coordinateSourceMeasure.restrict V) < ∞ := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily sourceChart
    sourceDensity coordinateSourceMeasure hJ hsource
  classical
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  haveI : IsFiniteMeasure passiveMeasure := ⟨hpassive_lt_top⟩
  rcases
      exists_matrixEntryReference_open_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_of_measure_le_smul_restrict_sourceCylinder_restrict_of_base_reindexed_det_isUnit
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext
        passiveMeasure hpassive_lt_top (t := t) Rres ht hRres hcrit
        eNext e z₀ V hF₀det with
    ⟨followingPatch, K, hK_pos, hF₀_mem, hpatch_open, hpatch_meas,
      hpatch_lt_top, hpatch_det, hpatch_inv_bound, hfinite_target⟩
  refine
    ⟨followingPatch, K, hK_pos, hF₀_mem, hpatch_open, hpatch_meas,
      hpatch_lt_top, hpatch_det, hpatch_inv_bound, ?_⟩
  intro productResidual hV_following
  let center : Finset (ℕ × ℕ) :=
    case2ResidualBlockPivotEntries n S (J + 1)
  let pivotNext : center :=
    case2PassiveThetaPivotNext n hS hnext
  let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
    Measure.pi
      (fun i : Case2PassiveTheta.Center n S J =>
        volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
  let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
    signedBox.withDensity
      (fun y : Case2PassiveTheta.Center n S J → ℝ =>
        ENNReal.ofReal
          (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
  let followingMeasure :=
    matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
  let sourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    ((passiveMeasure.prod weightedBox).prod followingMeasure).restrict
      {z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J |
        z.2 ∈ followingPatch}
  let localSourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    sourceMeasure.restrict V
  have hbase :
      referenceSource.restrict V ≤ Cpassive • localSourceMeasure := by
    simpa [ρ, referenceSource, localSourceMeasure, sourceMeasure,
      followingMeasure, weightedBox, signedBox] using
      case2PassiveThetaWithFollowingFactor_referenceSource_restrict_le_smul_sourceCylinder_restrict_of_passive_restrict_le_smul
        (ρ := ρ) (τ := τ) n hS hnext passiveMeasure Rres
        passiveLocalSet followingPatch V hpassive hV_passive hV_following
  have hcoordinate :
      (CS * (CJ * Cpassive)) < ∞ ∧
        coordinateSourceMeasure.restrict V ≤
          (CS * (CJ * Cpassive)) • localSourceMeasure := by
    simpa [RawTuple, Y, referenceSource, jacobianDensity, baseJ, EdgeFamily,
      sourceChart, sourceDensity, coordinateSourceMeasure, localSourceMeasure] using
      case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_restrict_le_smul_of_referenceSource_restrict_le_smul_of_lt_top
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e sourceImageDensity Rres V localSourceMeasure
        (Cbase := Cpassive) (CJ := CJ) (CS := CS)
        hV hbase hJ hsource hCpassive hCJ hCS
  simpa [ρ, κ', productResidual] using
    hfinite_target.2 (coordinateSourceMeasure.restrict V)
      (CS * (CJ * Cpassive)) hcoordinate.2 hcoordinate.1

-- The concrete with-following statement specializes the source measure to the reference source.
/-- Conditional reverse raw-source domination for the concrete with-following
coordinate source measure from determinant-chart reverse domination and a
source-density lower bound.

This specializes the reverse `baseJ` raw-source domination theorem to
`case2PassiveThetaWithFollowingFactorReferenceSourceMeasure`, then uses the
elementary lower-density adapter for
`coordinateSourceMeasure = baseJ.withDensity sourceDensity`.  The determinant
chart domination and the lower bound on `sourceDensity` remain explicit
hypotheses.

The theorem does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image/source-rank coverage,
original source-prior transport, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
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
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
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
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
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
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure]
          {Cdet ε : ℝ≥0∞},
          rawHaar.restrict rawDetChart ≤
              Cdet • Measure.map Y (referenceSource.restrict V) →
            Cdet < ∞ →
              (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                ε ≠ 0 →
                  ε ≠ ∞ →
                    (Cdet * ε⁻¹) < ∞ ∧
                      rawHaar.restrict rawSourceSet ≤
                        (Cdet * ε⁻¹) •
                          Measure.map rawMap
                            (coordinateSourceMeasure.restrict V) := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily sourceChart
    sourceDensity coordinateSourceMeasure rawMap rawDetChart rawSourceSet
  rcases
      (by
        simpa [referenceSource, Y, jacobianDensity, baseJ, rawMap, rawDetChart,
          rawSourceSet] using
          exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ referenceSource G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hrawMap_baseJ, hbase_dom⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawHaar _instRawHaar Cdet ε hdet_dom hCdet hlower hε0 hεtop
  have hrawMap_coordinate :
      AEMeasurable rawMap (coordinateSourceMeasure.restrict V) := by
    have hcoordinate_ac :
        coordinateSourceMeasure.restrict V ≪ baseJ.restrict V := by
      change (baseJ.withDensity sourceDensity).restrict V ≪ baseJ.restrict V
      rw [restrict_withDensity hVopen.measurableSet]
      exact withDensity_absolutelyContinuous _ _
    exact hrawMap_baseJ.mono_ac hcoordinate_ac
  have hdom :
      rawHaar.restrict rawSourceSet ≤
        (Cdet * ε⁻¹) •
          Measure.map rawMap ((baseJ.withDensity sourceDensity).restrict V) :=
    measure_le_smul_map_restrict_withDensity_of_le_smul_map_restrict_of_ae_le
      (base := baseJ) (target := rawHaar.restrict rawSourceSet)
      (rawMap := rawMap) (density := sourceDensity) (V := V)
      (D := Cdet) (ε := ε)
      hrawMap_coordinate hVopen.measurableSet
      (hbase_dom rawHaar hdet_dom) hlower hε0 hεtop
  have hfinite : Cdet * ε⁻¹ < ∞ := by
    exact ENNReal.mul_lt_top hCdet
      (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hε0))
  have hdom_coordinate :
      rawHaar.restrict rawSourceSet ≤
        (Cdet * ε⁻¹) •
          Measure.map rawMap (coordinateSourceMeasure.restrict V) := by
    change rawHaar.restrict rawSourceSet ≤
      (Cdet * ε⁻¹) •
        Measure.map rawMap ((baseJ.withDensity sourceDensity).restrict V)
    exact hdom
  exact ⟨hfinite, hdom_coordinate⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This localized coordinate-source wrapper replays the concrete global theorem
-- with the patch-parametric reverse base theorem in place of the global raw-source one.
/-- Localized conditional reverse raw-patch domination for the concrete
with-following coordinate source measure.

This is the patch-parametric form of
`exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower`:
the determinant-side input is localized to
`rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P`, and the conclusion is domination
of `rawHaar.restrict P`.

The endpoint-patch domination and source-density lower bound remain explicit
hypotheses.  The theorem does not prove determinant-chart Haar transport,
exact raw-Haar pushforward, raw-Haar normalization, source-image/source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
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
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
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
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
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
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure]
          {P : Set RawTuple} {Cdet ε : ℝ≥0∞},
          P ⊆ rawSourceSet →
            NullMeasurableSet (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) rawHaar →
              rawHaar.restrict (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) ≤
                  Cdet • Measure.map Y (referenceSource.restrict V) →
                Cdet < ∞ →
                  (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                    ε ≠ 0 →
                      ε ≠ ∞ →
                        (Cdet * ε⁻¹) < ∞ ∧
                          rawHaar.restrict P ≤
                            (Cdet * ε⁻¹) •
                              Measure.map rawMap
                                (coordinateSourceMeasure.restrict V) := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily sourceChart
    sourceDensity coordinateSourceMeasure rawMap rawOrderOnEndpoint rawDetChart
    rawSourceSet
  rcases
      (by
        simpa [referenceSource, Y, jacobianDensity, baseJ, rawMap,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet] using
          exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ referenceSource G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hrawMap_baseJ, hbase_dom⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawHaar _instRawHaar P Cdet ε hP hendpoint_nm hdet_dom hCdet
    hlower hε0 hεtop
  have hrawMap_coordinate :
      AEMeasurable rawMap (coordinateSourceMeasure.restrict V) := by
    have hcoordinate_ac :
        coordinateSourceMeasure.restrict V ≪ baseJ.restrict V := by
      change (baseJ.withDensity sourceDensity).restrict V ≪ baseJ.restrict V
      rw [restrict_withDensity hVopen.measurableSet]
      exact withDensity_absolutelyContinuous _ _
    exact hrawMap_baseJ.mono_ac hcoordinate_ac
  have hdom :
      rawHaar.restrict P ≤
        (Cdet * ε⁻¹) •
          Measure.map rawMap ((baseJ.withDensity sourceDensity).restrict V) :=
    measure_le_smul_map_restrict_withDensity_of_le_smul_map_restrict_of_ae_le
      (base := baseJ) (target := rawHaar.restrict P)
      (rawMap := rawMap) (density := sourceDensity) (V := V)
      (D := Cdet) (ε := ε)
      hrawMap_coordinate hVopen.measurableSet
      (hbase_dom rawHaar (P := P) (c := Cdet) hP hendpoint_nm hdet_dom)
      hlower hε0 hεtop
  have hfinite : Cdet * ε⁻¹ < ∞ := by
    exact ENNReal.mul_lt_top hCdet
      (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hε0))
  have hdom_coordinate :
      rawHaar.restrict P ≤
        (Cdet * ε⁻¹) •
          Measure.map rawMap (coordinateSourceMeasure.restrict V) := by
    change rawHaar.restrict P ≤
      (Cdet * ε⁻¹) •
        Measure.map rawMap ((baseJ.withDensity sourceDensity).restrict V)
    exact hdom
  exact ⟨hfinite, hdom_coordinate⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The localized eventual wrapper first shrinks to the lower-density neighborhood,
-- then invokes the patch-parametric coordinate-source theorem.
/-- Localized conditional reverse raw-patch domination from an eventual
source-density lower bound.

This is the patch-parametric topological wrapper around
`..._sourceDensity_lower`: an eventual lower bound for
`sourceImageDensity (sourceChart z)` near the base point is converted, after
shrinking, into the a.e. lower bound required by the localized lower-density
handoff.  The endpoint-patch domination and eventual lower bound remain
explicit hypotheses; no determinant Haar transport or density positivity
theorem is proved. -/
theorem exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple_eventually_sourceDensity_lower
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
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    {ε : ℝ≥0∞}
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
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawOrderOnEndpoint : RawTuple → RawTuple :=
      fun y ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y
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
    (∀ᶠ z in nhds z₀, ε ≤ sourceDensity z) →
      ∃ V :
        Set
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
          ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure]
            {P : Set RawTuple} {Cdet : ℝ≥0∞},
            P ⊆ rawSourceSet →
              NullMeasurableSet (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) rawHaar →
                rawHaar.restrict (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P) ≤
                    Cdet • Measure.map Y (referenceSource.restrict V) →
                  Cdet < ∞ →
                    ε ≠ 0 →
                      ε ≠ ∞ →
                        (Cdet * ε⁻¹) < ∞ ∧
                          rawHaar.restrict P ≤
                            (Cdet * ε⁻¹) •
                              Measure.map rawMap
                                (coordinateSourceMeasure.restrict V) := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily
    sourceChart sourceDensity coordinateSourceMeasure rawMap rawOrderOnEndpoint
    rawDetChart rawSourceSet hsource_eventually
  rcases eventually_nhds_iff.mp hsource_eventually with
    ⟨H, hHlower, hHopen, hz₀H⟩
  rcases
      (by
        simpa [referenceSource, Y, jacobianDensity, baseJ, EdgeFamily,
          sourceChart, sourceDensity, coordinateSourceMeasure, rawMap,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet] using
          exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_endpointPatch_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres (G ∩ H)
            (hGopen.inter hHopen) ⟨hz₀G, hz₀H⟩) with
    ⟨V, hVopen, hz₀V, hVGH, hraw_dom⟩
  have hVG : V ⊆ G := hVGH.1
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawHaar _instRawHaar P Cdet hP hendpoint_nm hdet_dom hCdet hε0
    hεtop
  have hlower :
      ∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hzV
    exact hHlower z (hVGH.2 hzV)
  exact
    hraw_dom rawHaar (P := P) (Cdet := Cdet) (ε := ε) hP hendpoint_nm
      hdet_dom hCdet hlower hε0 hεtop

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The eventual-bound wrapper chooses the lower-density neighborhood before the raw shrink.
/-- Conditional reverse raw-source domination from determinant-chart reverse
domination and an eventual source-density lower bound.

This is the topological wrapper around
`..._sourceDensity_lower`: an eventual lower bound for
`sourceImageDensity (sourceChart z)` near the base point is converted, after
shrinking, into the a.e. lower bound required by the lower-density handoff.
The determinant-chart domination and the eventual lower bound remain explicit
hypotheses; no determinant Haar transport or density positivity theorem is
proved. -/
theorem exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceDensity_lower
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
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    {ε : ℝ≥0∞}
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
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      referenceSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
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
    (∀ᶠ z in nhds z₀, ε ≤ sourceDensity z) →
      ∃ V :
        Set
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
          ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure]
            {Cdet : ℝ≥0∞},
            rawHaar.restrict rawDetChart ≤
                Cdet • Measure.map Y (referenceSource.restrict V) →
              Cdet < ∞ →
                ε ≠ 0 →
                  ε ≠ ∞ →
                    (Cdet * ε⁻¹) < ∞ ∧
                      rawHaar.restrict rawSourceSet ≤
                        (Cdet * ε⁻¹) •
                          Measure.map rawMap
                            (coordinateSourceMeasure.restrict V) := by
  intro RawTuple Y referenceSource jacobianDensity baseJ EdgeFamily
    sourceChart sourceDensity coordinateSourceMeasure rawMap rawDetChart
    rawSourceSet hsource_eventually
  rcases eventually_nhds_iff.mp hsource_eventually with
    ⟨H, hHlower, hHopen, hz₀H⟩
  rcases
      (by
        simpa [referenceSource, Y, jacobianDensity, baseJ, EdgeFamily,
          sourceChart, sourceDensity, coordinateSourceMeasure, rawMap,
          rawDetChart, rawSourceSet] using
          exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity Rres (G ∩ H)
            (hGopen.inter hHopen) ⟨hz₀G, hz₀H⟩) with
    ⟨V, hVopen, hz₀V, hVGH, hraw_dom⟩
  have hVG : V ⊆ G := hVGH.1
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawHaar _instRawHaar Cdet hdet_dom hCdet hε0 hεtop
  have hlower :
      ∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hzV
    exact hHlower z (hVGH.2 hzV)
  exact hraw_dom rawHaar hdet_dom hCdet hlower hε0 hεtop

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the passive-theta chart interface.
/-- Passive-field domination transfers determinant-chart endpoint domination
to the corresponding passive-product theta source.

This is the adapter needed for a future concrete passive-field Haar/Lebesgue
reference.  If `passiveMeasure` is dominated by `d` times a passive reference
measure, and the reference product source already satisfies the endpoint
determinant-chart domination with scalar `c`, then the product source built
from `passiveMeasure` satisfies the same domination with scalar `d * c`.

The determinant-chart domination for the reference source remains explicit.
This theorem does not construct the reference source, prove passive-product
Haar transport, normalize Haar scalars, identify a source prior, prove normal
crossings, pole order, or RLCT extraction. -/
theorem measure_map_case2PassiveThetaEndpointTopologyTuple_passiveSource_restrict_le_smul_detChart_of_passiveMeasure_le_smul_reference
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
      (Case2PassiveTheta.PassiveFields
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
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (passiveMeasure passiveReferenceMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let passiveReferenceSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveReferenceMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    ∀ (rawReference : Measure RawTuple) {c d : ℝ≥0∞},
      passiveMeasure ≤ d • passiveReferenceMeasure →
        Measure.map Y (passiveReferenceSource.restrict V) ≤
            c • rawReference.restrict rawDetChart →
          Measure.map Y (passiveSource.restrict V) ≤
            (d * c) • rawReference.restrict rawDetChart := by
  intro center pivotNext signedBox weightedBox passiveSource
    passiveReferenceSource RawTuple Y rawDetChart rawReference c d
    hpassive_dom href_dom
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  haveI : SFinite weightedBox := by infer_instance
  have hY :
      AEMeasurable Y (passiveReferenceSource.restrict V) := by
    have hYcont : Continuous Y := by
      simpa [Y, RawTuple, ρ, κ'] using
        continuous_case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hsource_dom :
      passiveSource.restrict V ≤ d • passiveReferenceSource.restrict V := by
    change (passiveMeasure.prod weightedBox).restrict V ≤
      d • (passiveReferenceMeasure.prod weightedBox).restrict V
    have hprod :
        passiveMeasure.prod weightedBox ≤
          d • passiveReferenceMeasure.prod weightedBox :=
      prod_le_smul_prod_of_le_smul_left (η := weightedBox) hpassive_dom
    calc
      (passiveMeasure.prod weightedBox).restrict V ≤
          (d • passiveReferenceMeasure.prod weightedBox).restrict V :=
        Measure.restrict_mono Set.Subset.rfl hprod
      _ = d • (passiveReferenceMeasure.prod weightedBox).restrict V := by
        rw [Measure.restrict_smul]
  have hmap :
      Measure.map Y (passiveSource.restrict V) ≤
        d • Measure.map Y (passiveReferenceSource.restrict V) :=
    map_le_smul_map_of_le_smul_aemeasurable hY hsource_dom
  exact measure_le_smul_of_le_smul_of_le_smul hmap href_dom

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the passive-theta chart and raw-order interfaces.
/-- Concrete raw-image density formula using raw-order inverse readback.

This specializes
`exists_open_subset_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_eq_withDensity_rawImage_of_jacobianDensity_ae_eq`
to the raw-side density obtained by evaluating the same retained-passive
source-side Jacobian product at `topologyTupleEdgeRawOrderInverse y`.

This is not the target-side inverse Jacobian density.  The conclusion is still
over the actual raw image `Measure.map rawMap (passiveSource.restrict V)`, not
over raw Haar restricted to the raw-order source set. -/
theorem exists_open_subset_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_eq_withDensity_rawImage_rawOrderInverse_jacobianDensity
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
      (Case2PassiveTheta.PassiveFields
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
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
            (topologyTupleEdgeRawOrderInverse
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y))
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        Measure.map rawMap (baseJ.restrict V) =
          (Measure.map rawMap (passiveSource.restrict V)).withDensity
            rawDensity := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple Y
    jacobianDensity baseJ rawMap rawDensity
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, _hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let T : Set RawTuple :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
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
  have hrawMap :
      AEMeasurable rawMap (passiveSource.restrict V) := by
    exact
      ContinuousOn.aemeasurable₀ hrawMapContOn
        hVopen.measurableSet.nullMeasurableSet
  have hraw_mem :
      ∀ᵐ z ∂passiveSource.restrict V, rawMap z ∈ T := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    simpa [rawMap, T, RawTuple, ρ, κ'] using (hpoint z hz).2.1
  have hT_meas : MeasurableSet T := by
    simpa [T, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hraw_image_mem :
      ∀ᵐ y ∂Measure.map rawMap (passiveSource.restrict V), y ∈ T :=
    (ae_map_iff hrawMap hT_meas).2 hraw_mem
  have hrawDensityContOn : ContinuousOn rawDensity T := by
    rw [continuousOn_iff_continuous_restrict]
    rw [continuous_iff_continuousAt]
    intro y
    let invMap : T → RawTuple :=
      fun y ↦ topologyTupleEdgeRawOrderInverse
        (K := ℝ) (ρ := ρ) (κ' := κ') y.1
    have hInv :
        Continuous invMap :=
      continuous_topologyTupleEdgeRawOrderInverse_rawOrderSourceRecursiveDetChart_subtype
        (K := ℝ) (ρ := ρ) (κ' := κ')
    have hpre :
        invMap y ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
      simpa [invMap] using
        topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ') y.2
    have hreal :
        ContinuousAt
          (fun y : T ↦
            retainedPassiveFormalRawOrderJacobianProductAbsDetAt
              (M := 1) (ρ := ρ) (κ' := κ') (invMap y)) y :=
      (continuousAt_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_of_mem_topologyTupleDetChartSet
        (M := 1) (ρ := ρ) (κ' := κ') (invMap y) hpre).comp hInv.continuousAt
    simpa [rawDensity, invMap, RawTuple, ρ, κ'] using
      ENNReal.continuous_ofReal.continuousAt.comp hreal
  have hrawDensity_restrict :
      AEMeasurable rawDensity
        ((Measure.map rawMap (passiveSource.restrict V)).restrict T) :=
    ContinuousOn.aemeasurable₀ hrawDensityContOn hT_meas.nullMeasurableSet
  have hraw_restrict_eq :
      (Measure.map rawMap (passiveSource.restrict V)).restrict T =
        Measure.map rawMap (passiveSource.restrict V) :=
    Measure.restrict_eq_self_of_ae_mem hraw_image_mem
  have hrawDensity :
      AEMeasurable rawDensity
        (Measure.map rawMap (passiveSource.restrict V)) := by
    simpa [hraw_restrict_eq] using hrawDensity_restrict
  have hfactor :
      ∀ᵐ z ∂passiveSource.restrict V,
        jacobianDensity z = rawDensity (rawMap z) := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    have hInv :
        topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ')
            (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') (Y z)) =
          Y z :=
      topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := ρ) (κ' := κ') (hdet_of_mem z hz)
    simp [jacobianDensity, rawDensity, rawMap, RawTuple, ρ, κ', hInv]
  simpa [baseJ] using
    DLNFibre.DLN.Aoyagi.measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq
      (thetaMeasure := passiveSource) (V := V) (rawMap := rawMap)
      (thetaDensity := jacobianDensity) (rawDensity := rawDensity)
      hVopen.measurableSet hrawMap hrawDensity hfactor

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the passive-theta chart and raw-order interfaces.
/-- Conditional determinant-Haar to raw-order inverse-Jacobian domination.

On a local Case 2 determinant/pivot sector, suppose the endpoint topology-tuple
pushforward of the unweighted passive-product theta reference is dominated by a
scalar multiple of additive Haar restricted to the retained-passive
determinant chart.  Then the raw-order pushforward is dominated by the same
scalar multiple of the raw-order Haar measure weighted by the retained-passive
inverse-Jacobian density.

The determinant-chart domination hypothesis is explicit.  This theorem does
not prove passive-product Haar transport, identify the raw image with raw
Haar, normalize Haar scalars, prove source-image/source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_measure_map_case2PassiveTheta_rawMap_passiveSource_restrict_le_smul_rawHaar_withDensity_inverseJacobian_of_endpointTopologyTuple_restrict_le_smul_detHaar
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
      (Case2PassiveTheta.PassiveFields
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
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
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
    let rawInverseJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (topologyTupleEdgeRawOrderInverseJacobianDensity
            (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        AEMeasurable rawMap (passiveSource.restrict V) ∧
          ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure] {c : ℝ≥0∞},
            Measure.map Y (passiveSource.restrict V) ≤
                c • rawHaar.restrict rawDetChart →
              Measure.map rawMap (passiveSource.restrict V) ≤
                c • ((rawHaar.restrict rawSourceSet).withDensity
                  rawInverseJacobianDensity) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple Y rawMap
    rawDetChart rawSourceSet rawInverseJacobianDensity
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, _hmaps⟩
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let Φ : RawTuple → RawTuple :=
    fun y ↦
      topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
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
  have hrawMap :
      AEMeasurable rawMap (passiveSource.restrict V) :=
    ContinuousOn.aemeasurable₀ hrawMapContOn
      hVopen.measurableSet.nullMeasurableSet
  refine ⟨V, hVopen, hz₀V, hVG, hrawMap, ?_⟩
  intro rawHaar _instRawHaar c hYdom
  have hY :
      AEMeasurable Y (passiveSource.restrict V) := by
    have hYcont : Continuous Y := by
      simpa [Y, RawTuple, ρ, κ'] using
        continuous_case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hdet_nm :
      NullMeasurableSet rawDetChart rawHaar := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      nullMeasurableSet_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') rawHaar
  have hΦ_ref :
      AEMeasurable Φ (rawHaar.restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ_ref_map :
      Measure.map Φ (rawHaar.restrict rawDetChart) =
        (rawHaar.restrict rawSourceSet).withDensity
          rawInverseJacobianDensity := by
    simpa [Φ, rawDetChart, rawSourceSet, rawInverseJacobianDensity,
      RawTuple, ρ, κ'] using
      map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
        (M := 1) (ρ := ρ) (κ' := κ') rawHaar hdet_nm
  simpa [rawMap, Φ, RawTuple, ρ, κ'] using
    DLNFibre.DLN.Aoyagi.map_comp_le_smul_of_map_le_smul_of_map_ref_eq
      (μ := passiveSource.restrict V)
      (sourceRef := rawHaar.restrict rawDetChart)
      (targetRef :=
        (rawHaar.restrict rawSourceSet).withDensity rawInverseJacobianDensity)
      (pre := Y) (post := Φ) hY hΦ_ref hYdom hΦ_ref_map

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the passive-theta chart and raw-order interfaces.
/-- Conditional determinant-Haar to raw-Haar domination for the globally
Jacobian-weighted Case 2 passive-theta reference.

On a local Case 2 determinant/pivot sector, suppose the endpoint topology-tuple
pushforward of the unweighted passive-product theta reference is dominated by a
scalar multiple of additive Haar restricted to the retained-passive determinant
chart.  Then the raw-order pushforward of
`baseJ = passiveSource.withDensity jacobianDensity` is dominated by the same
scalar multiple of additive Haar restricted to the raw-order source-recursive
determinant chart.

The determinant-chart domination hypothesis remains explicit.  This theorem
uses the retained-passive formal-product Jacobian change-of-variables theorem;
it does not prove passive-product Haar transport, exact raw-Haar pushforward,
raw-Haar normalization, source-image/source-rank coverage, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_open_subset_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_le_smul_rawHaar_restrict_rawSource_of_endpointTopologyTuple_restrict_le_smul_detHaar
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
      (Case2PassiveTheta.PassiveFields
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
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
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
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure] {c : ℝ≥0∞},
          Measure.map Y (passiveSource.restrict V) ≤
              c • rawHaar.restrict rawDetChart →
            Measure.map rawMap (baseJ.restrict V) ≤
              c • rawHaar.restrict rawSourceSet := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple Y
    jacobianDensity baseJ rawMap rawDetChart rawSourceSet
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, _hpoint, _hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawHaar _instRawHaar c hYdom
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let Φ : RawTuple → RawTuple :=
    fun y ↦
      topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
  let formalDensity : RawTuple → ℝ≥0∞ :=
    fun y ↦
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := 1) (ρ := ρ) (κ' := κ') y)
  have hY :
      AEMeasurable Y (passiveSource.restrict V) := by
    have hYcont : Continuous Y := by
      simpa [Y, RawTuple, ρ, κ'] using
        continuous_case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hdet_nm :
      NullMeasurableSet rawDetChart rawHaar := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      nullMeasurableSet_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') rawHaar
  have hformalDensity_ref :
      AEMeasurable formalDensity (rawHaar.restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm
    intro y hy
    exact
      (ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_of_mem_topologyTupleDetChartSet
          (M := 1) (ρ := ρ) (κ' := κ') y (by
            simpa [rawDetChart, RawTuple, ρ, κ'] using hy))).continuousWithinAt
  have hΦ_ref :
      AEMeasurable Φ (rawHaar.restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ_ref_weighted :
      AEMeasurable Φ ((rawHaar.restrict rawDetChart).withDensity formalDensity) :=
    hΦ_ref.mono_ac (withDensity_absolutelyContinuous _ _)
  have hΦ_ref_map :
      Measure.map Φ ((rawHaar.restrict rawDetChart).withDensity formalDensity) =
        rawHaar.restrict rawSourceSet := by
    simpa [Φ, formalDensity, rawDetChart, rawSourceSet, RawTuple, ρ, κ'] using
      map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart
        (M := 1) (ρ := ρ) (κ' := κ') rawHaar hdet_nm
  have hbase_restrict :
      baseJ.restrict V =
        (passiveSource.restrict V).withDensity (fun z ↦ formalDensity (Y z)) := by
    change (passiveSource.withDensity jacobianDensity).restrict V =
      (passiveSource.restrict V).withDensity (fun z ↦ formalDensity (Y z))
    rw [restrict_withDensity hVopen.measurableSet]
  have hweighted :
      Measure.map (fun z ↦ Φ (Y z))
          ((passiveSource.restrict V).withDensity (fun z ↦ formalDensity (Y z))) ≤
        c • rawHaar.restrict rawSourceSet :=
    DLNFibre.DLN.Aoyagi.map_comp_withDensity_comp_le_smul_of_map_le_smul_of_weighted_map_ref_eq
      (μ := passiveSource.restrict V)
      (sourceRef := rawHaar.restrict rawDetChart)
      (targetRef := rawHaar.restrict rawSourceSet)
      (pre := Y) (post := Φ) (density := formalDensity)
      hY hformalDensity_ref hΦ_ref_weighted hYdom hΦ_ref_map
  calc
    Measure.map rawMap (baseJ.restrict V) =
        Measure.map rawMap
          ((passiveSource.restrict V).withDensity (fun z ↦ formalDensity (Y z))) := by
          rw [hbase_restrict]
    _ ≤ c • rawHaar.restrict rawSourceSet := by
          simpa [rawMap, Φ, RawTuple, ρ, κ'] using hweighted

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the passive-theta chart and raw-order interfaces.
/-- Conditional reverse determinant-Haar to raw-Haar domination for the
globally Jacobian-weighted Case 2 passive-theta reference.

On a local Case 2 determinant/pivot sector, suppose additive Haar restricted
to the retained-passive determinant chart is dominated by a scalar multiple of
the endpoint topology-tuple pushforward of the unweighted passive-product
theta reference.  Then additive Haar restricted to the raw-order
source-recursive determinant chart is dominated by the same scalar multiple of
the raw-order pushforward of
`baseJ = passiveSource.withDensity jacobianDensity`.

The determinant-chart reverse domination hypothesis remains explicit.  This
theorem uses the retained-passive formal-product Jacobian change-of-variables
theorem; it does not prove passive-product Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image/source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
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
      (Case2PassiveTheta.PassiveFields
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
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
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
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        AEMeasurable rawMap (baseJ.restrict V) ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure] {c : ℝ≥0∞},
          rawHaar.restrict rawDetChart ≤
              c • Measure.map Y (passiveSource.restrict V) →
            rawHaar.restrict rawSourceSet ≤
              c • Measure.map rawMap (baseJ.restrict V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple Y
    jacobianDensity baseJ rawMap rawDetChart rawSourceSet
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, _hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_, ?_⟩
  · let ρ := Fin (Module.finrank ℝ U₀)
    let κ' : Fin 3 → Type :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    have hdet_of_mem :
        ∀ z ∈ V,
          Y z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
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
    exact
      ContinuousOn.aemeasurable₀ hrawMapContOn
        hVopen.measurableSet.nullMeasurableSet
  intro rawHaar _instRawHaar c hYdom
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let Φ : RawTuple → RawTuple :=
    fun y ↦
      topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
  let formalDensity : RawTuple → ℝ≥0∞ :=
    fun y ↦
      ENNReal.ofReal
        (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
          (M := 1) (ρ := ρ) (κ' := κ') y)
  have hY :
      AEMeasurable Y (passiveSource.restrict V) := by
    have hYcont : Continuous Y := by
      simpa [Y, RawTuple, ρ, κ'] using
        continuous_case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hdet_meas : MeasurableSet rawDetChart := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hdet_nm_rawHaar :
      NullMeasurableSet rawDetChart rawHaar := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      nullMeasurableSet_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') rawHaar
  have hY_mem :
      ∀ᵐ z ∂passiveSource.restrict V, Y z ∈ rawDetChart := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    simpa [Y, rawDetChart, RawTuple, ρ, κ'] using (hpoint z hz).1
  have hmapY_mem :
      ∀ᵐ y ∂Measure.map Y (passiveSource.restrict V),
        y ∈ rawDetChart :=
    (ae_map_iff hY hdet_meas).2 hY_mem
  have hmapY_restrict :
      (Measure.map Y (passiveSource.restrict V)).restrict rawDetChart =
        Measure.map Y (passiveSource.restrict V) :=
    Measure.restrict_eq_self_of_ae_mem hmapY_mem
  have hdet_nm_mapY :
      NullMeasurableSet rawDetChart (Measure.map Y (passiveSource.restrict V)) :=
    hdet_meas.nullMeasurableSet
  have hformalDensity_map_restrict :
      AEMeasurable formalDensity
        ((Measure.map Y (passiveSource.restrict V)).restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm_mapY
    intro y hy
    exact
      (ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_of_mem_topologyTupleDetChartSet
          (M := 1) (ρ := ρ) (κ' := κ') y (by
            simpa [rawDetChart, RawTuple, ρ, κ'] using hy))).continuousWithinAt
  have hformalDensity_map :
      AEMeasurable formalDensity
        (Measure.map Y (passiveSource.restrict V)) := by
    simpa [hmapY_restrict] using hformalDensity_map_restrict
  have hΦ_map_restrict :
      AEMeasurable Φ
        ((Measure.map Y (passiveSource.restrict V)).restrict rawDetChart) := by
    refine ContinuousOn.aemeasurable₀ ?_ hdet_nm_mapY
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ_map :
      AEMeasurable Φ (Measure.map Y (passiveSource.restrict V)) := by
    simpa [hmapY_restrict] using hΦ_map_restrict
  have hΦ_map_weighted :
      AEMeasurable Φ
        ((Measure.map Y (passiveSource.restrict V)).withDensity
          formalDensity) :=
    hΦ_map.mono_ac (withDensity_absolutelyContinuous _ _)
  have hΦ_ref_map :
      Measure.map Φ ((rawHaar.restrict rawDetChart).withDensity formalDensity) =
        rawHaar.restrict rawSourceSet := by
    simpa [Φ, formalDensity, rawDetChart, rawSourceSet, RawTuple, ρ, κ'] using
      map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_rawSourceChart
        (M := 1) (ρ := ρ) (κ' := κ') rawHaar hdet_nm_rawHaar
  have hbase_restrict :
      baseJ.restrict V =
        (passiveSource.restrict V).withDensity (fun z ↦ formalDensity (Y z)) := by
    change (passiveSource.withDensity jacobianDensity).restrict V =
      (passiveSource.restrict V).withDensity (fun z ↦ formalDensity (Y z))
    rw [restrict_withDensity hVopen.measurableSet]
  have hweighted :
      rawHaar.restrict rawSourceSet ≤
        c • Measure.map (fun z ↦ Φ (Y z))
          ((passiveSource.restrict V).withDensity
            (fun z ↦ formalDensity (Y z))) :=
    DLNFibre.DLN.Aoyagi.weighted_map_ref_le_smul_map_comp_withDensity_comp_of_le_smul_map
      (μ := passiveSource.restrict V)
      (sourceRef := rawHaar.restrict rawDetChart)
      (targetRef := rawHaar.restrict rawSourceSet)
      (pre := Y) (post := Φ) (density := formalDensity)
      hY hformalDensity_map hΦ_map_weighted hYdom hΦ_ref_map
  have htarget_eq :
      Measure.map (fun z ↦ Φ (Y z))
          ((passiveSource.restrict V).withDensity
            (fun z ↦ formalDensity (Y z))) =
        Measure.map rawMap (baseJ.restrict V) := by
    rw [hbase_restrict]
  calc
    rawHaar.restrict rawSourceSet ≤
        c • Measure.map (fun z ↦ Φ (Y z))
          ((passiveSource.restrict V).withDensity
            (fun z ↦ formalDensity (Y z))) := hweighted
    _ = c • Measure.map rawMap (baseJ.restrict V) := by
          rw [htarget_eq]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the passive-theta chart and raw-order interfaces.
/-- Conditional reverse raw-source domination for the concrete coordinate
source measure from determinant-chart reverse domination and a source-density
lower bound.

This applies the reverse `baseJ` raw-source domination theorem and then uses
the elementary lower-density adapter for
`coordinateSourceMeasure = baseJ.withDensity sourceDensity`.  The determinant
chart domination and the lower bound on `sourceDensity` remain explicit
hypotheses.

The theorem does not prove determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image/source-rank coverage,
original source-prior transport, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
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
      (Case2PassiveTheta.PassiveFields
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
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
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure]
          {Cdet ε : ℝ≥0∞},
          rawHaar.restrict rawDetChart ≤
              Cdet • Measure.map Y (passiveSource.restrict V) →
            Cdet < ∞ →
              (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                ε ≠ 0 →
                  ε ≠ ∞ →
                    (Cdet * ε⁻¹) < ∞ ∧
                      rawHaar.restrict rawSourceSet ≤
                        (Cdet * ε⁻¹) •
                          Measure.map rawMap
                            (coordinateSourceMeasure.restrict V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple Y
    jacobianDensity baseJ EdgeFamily sourceChart sourceDensity
    coordinateSourceMeasure rawMap rawDetChart rawSourceSet
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, rawMap, rawDetChart, rawSourceSet] using
          exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ passiveMeasure Rres G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hrawMap_baseJ, hbase_dom⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawHaar _instRawHaar Cdet ε hdet_dom hCdet hlower hε0 hεtop
  have hrawMap_coordinate :
      AEMeasurable rawMap (coordinateSourceMeasure.restrict V) := by
    have hcoordinate_ac :
        coordinateSourceMeasure.restrict V ≪ baseJ.restrict V := by
      change (baseJ.withDensity sourceDensity).restrict V ≪ baseJ.restrict V
      rw [restrict_withDensity hVopen.measurableSet]
      exact withDensity_absolutelyContinuous _ _
    exact hrawMap_baseJ.mono_ac hcoordinate_ac
  have hdom :
      rawHaar.restrict rawSourceSet ≤
        (Cdet * ε⁻¹) •
          Measure.map rawMap ((baseJ.withDensity sourceDensity).restrict V) :=
    measure_le_smul_map_restrict_withDensity_of_le_smul_map_restrict_of_ae_le
      (base := baseJ) (target := rawHaar.restrict rawSourceSet)
      (rawMap := rawMap) (density := sourceDensity) (V := V)
      (D := Cdet) (ε := ε)
      hrawMap_coordinate hVopen.measurableSet
      (hbase_dom rawHaar hdet_dom) hlower hε0 hεtop
  have hfinite : Cdet * ε⁻¹ < ∞ := by
    exact ENNReal.mul_lt_top hCdet
      (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hε0))
  have hdom_coordinate :
      rawHaar.restrict rawSourceSet ≤
        (Cdet * ε⁻¹) •
          Measure.map rawMap (coordinateSourceMeasure.restrict V) := by
    change rawHaar.restrict rawSourceSet ≤
      (Cdet * ε⁻¹) •
        Measure.map rawMap ((baseJ.withDensity sourceDensity).restrict V)
    exact hdom
  exact ⟨hfinite, hdom_coordinate⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the passive-theta chart and raw-order interfaces.
/-- Same-shrink package for the Case 2 source chart and reverse raw-source
domination from determinant-chart reverse domination plus a source-density
lower bound.

The theorem first chooses a source-chart/readback shrink, then a two-stage
raw-order/source-chart shrink, and finally a reverse raw-source density shrink.
The returned `V` carries the source-chart image data and the raw-source
domination on the same set.

The determinant-chart reverse domination and the lower bound on
`sourceDensity` remain explicit hypotheses.  This theorem does not prove
determinant-chart Haar transport, exact raw-Haar pushforward, raw-Haar
normalization, source-image/source-rank coverage, original source-prior
transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_case2PassiveTheta_sourceChart_rawMap_coordinateSourceMeasure_reverse_domination_package_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
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
      (Case2PassiveTheta.PassiveFields
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    let sourceDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure := baseJ.withDensity sourceDensity
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
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (sourceChart '' V) ∧
              (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                (∀ z ∈ V, rawMap z ∈ rawSourceSet) ∧
                  AEMeasurable rawMap (coordinateSourceMeasure.restrict V) ∧
                (∀ sourceMeasure :
                  Measure
                    (Case2PassiveTheta
                      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                  let ν := sourceMeasure.restrict V
                  let μ := Measure.map sourceChart ν
                  let μrawComp := Measure.map (fun z ↦ rawChart (rawMap z)) ν
                  let μrawTwoStage := Measure.map rawChart (Measure.map rawMap ν)
                  μrawComp = μ ∧ μrawTwoStage = μ) ∧
                  ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure]
                    {Cdet ε : ℝ≥0∞},
                    rawHaar.restrict rawDetChart ≤
                        Cdet • Measure.map Y (passiveSource.restrict V) →
                      Cdet < ∞ →
                        (∀ᵐ z ∂baseJ.restrict V, ε ≤ sourceDensity z) →
                          ε ≠ 0 →
                            ε ≠ ∞ →
                              (Cdet * ε⁻¹) < ∞ ∧
                                rawHaar.restrict rawSourceSet ≤
                                  (Cdet * ε⁻¹) •
                                    Measure.map rawMap
                                      (coordinateSourceMeasure.restrict V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple
    EdgeFamily Y rawMap rawChart jacobianDensity baseJ sourceChart readback
    sourceDensity coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback, p13SourceSet] using
          exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨Vsrc, hVsrc_open, hz₀Vsrc, hVsrcG, _hdet_src, hleft_src,
      hsource_inj_src, hsource_contOn_src, _hsource_image_src,
      _hpoint_p13_src, himage_p13_src⟩
  rcases
      (by
        simpa [center, EdgeFamily, sourceChart, rawMap, rawChart, Y] using
          exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ Vsrc hVsrc_open hz₀Vsrc) with
    ⟨Vtwo, hVtwo_open, hz₀Vtwo, hVtwo_src, _hsector_two, hpoint_two,
      hmeasure_maps_two⟩
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, Y, jacobianDensity, baseJ, EdgeFamily, sourceChart,
          sourceDensity, coordinateSourceMeasure, rawMap, rawDetChart,
          rawSourceSet] using
          exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres Vtwo
            hVtwo_open hz₀Vtwo) with
    ⟨V, hVopen, hz₀V, hV_two, hraw_dom⟩
  have hV_src : V ⊆ Vsrc := fun z hz ↦ hVtwo_src (hV_two hz)
  have hVG : V ⊆ G := fun _ hz ↦ hVsrcG (hV_src hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈
          Vsrc := by
      simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hV_src hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft_src z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz_fields
  have hsource_injV : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    exact hsource_inj_src (hV_src hz) (hV_src hz') hsrc
  have hsource_contOnV : ContinuousOn sourceChart V :=
    hsource_contOn_src.mono hV_src
  have hsource_imageV : MeasurableSet (sourceChart '' V) :=
    hVopen.measurableSet.image_of_continuousOn_injOn hsource_contOnV hsource_injV
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    have hz_fields :
        ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈
          Vsrc := by
      simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hV_src hzV
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13_src (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hz_fields rfl
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  have hdet_of_mem :
      ∀ z ∈ V,
        Y z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    intro z hz
    have hz_fields :
        ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈
          Vtwo := by
      simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hV_two hz
    have hpoint :=
      hpoint_two z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext
        hz_fields
    simpa [Y, RawTuple, ρ, κ'] using hpoint.1
  have hraw_memV : ∀ z ∈ V, rawMap z ∈ rawSourceSet := by
    intro z hz
    have hz_fields :
        ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈
          Vtwo := by
      simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hV_two hz
    have hpoint :=
      hpoint_two z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext
        hz_fields
    simpa [rawMap, rawSourceSet, RawTuple, ρ, κ'] using hpoint.2.1
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
  have hrawMap_aemeas :
      AEMeasurable rawMap (coordinateSourceMeasure.restrict V) := by
    simpa using
      ContinuousOn.aemeasurable₀ hrawMapContOn
        hVopen.measurableSet.nullMeasurableSet
  refine ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V, hraw_memV, hrawMap_aemeas, ?_, hraw_dom⟩
  intro sourceMeasure ν μ μrawComp μrawTwoStage
  have hmaps :=
    hmeasure_maps_two (sourceMeasure := sourceMeasure.restrict V)
  have hrestrict :
      (sourceMeasure.restrict V).restrict Vtwo =
        sourceMeasure.restrict V := by
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hVopen.measurableSet).mono (fun _ hzV ↦ hV_two hzV))
  simpa [ν, μ, μrawComp, μrawTwoStage, RawTuple, EdgeFamily, sourceChart,
    rawMap, rawChart, hrestrict] using hmaps

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete Case 2 statement unfolds the passive-theta chart and raw-order interfaces.
/-- Conditional raw-order inverse-Jacobian domination for the globally
Jacobian-weighted Case 2 passive-theta reference.

The theorem first shrinks to a local neighborhood where the retained-passive
forward Jacobian factor is bounded above by a constant `K`.  On a smaller
determinant/pivot sector, an explicit determinant-chart Haar domination
hypothesis for the unweighted passive source then implies raw-order domination
for `baseJ = passiveSource.withDensity jacobianDensity`, with scalar
`ofReal K * c`.

The determinant-chart domination hypothesis remains explicit.  This theorem
does not prove passive-product Haar transport, exact raw-Haar pushforward,
raw-Haar normalization, source-image/source-rank coverage, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_pos_open_subset_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_le_smul_rawHaar_withDensity_inverseJacobian_of_endpointTopologyTuple_restrict_le_smul_detHaar
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
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
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
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z)
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
    let rawInverseJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (topologyTupleEdgeRawOrderInverseJacobianDensity
            (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
    ∃ K : ℝ, 0 < K ∧
      ∃ V :
        Set
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
          ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure] {c : ℝ≥0∞},
            Measure.map Y (passiveSource.restrict V) ≤
                c • rawHaar.restrict rawDetChart →
              Measure.map rawMap (baseJ.restrict V) ≤
                (ENNReal.ofReal K * c) •
                  ((rawHaar.restrict rawSourceSet).withDensity
                    rawInverseJacobianDensity) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple Y
    jacobianDensity baseJ rawMap rawDetChart rawSourceSet
    rawInverseJacobianDensity
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity] using
          exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure
            W₂ B₂ n hS hcont hnext (U₀ := U₀) eNext e
            z₀ hdet₀ passiveMeasure Rres) with
    ⟨ε, _hε, K, hK, U, hUopen, hz₀U, _hlower, hupper⟩
  rcases
      exists_open_subset_measure_map_case2PassiveTheta_rawMap_passiveSource_restrict_le_smul_rawHaar_withDensity_inverseJacobian_of_endpointTopologyTuple_restrict_le_smul_detHaar
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ passiveMeasure Rres (G ∩ U)
        (hGopen.inter hUopen) ⟨hz₀G, hz₀U⟩ with
    ⟨V, hVopen, hz₀V, hVGU, hrawMap, hraw_dom⟩
  refine ⟨K, hK, V, hVopen, hz₀V, (fun z hz ↦ (hVGU hz).1), ?_⟩
  intro rawHaar _instRawHaar c hYdom
  have hVU : V ⊆ U := fun z hz ↦ (hVGU hz).2
  have hweighted_restrict :
      ((passiveSource.restrict U).withDensity jacobianDensity).restrict V ≤
        (ENNReal.ofReal K • passiveSource.restrict U).restrict V := by
    exact Measure.restrict_mono Set.Subset.rfl hupper
  have hrestrict_eq :
      baseJ.restrict V =
        ((passiveSource.restrict U).withDensity jacobianDensity).restrict V := by
    change (passiveSource.withDensity jacobianDensity).restrict V =
      ((passiveSource.restrict U).withDensity jacobianDensity).restrict V
    rw [restrict_withDensity hVopen.measurableSet,
      restrict_withDensity hVopen.measurableSet]
    rw [Measure.restrict_restrict_of_subset hVU]
  have hbase_dom :
      baseJ.restrict V ≤ ENNReal.ofReal K • passiveSource.restrict V := by
    calc
      baseJ.restrict V =
          ((passiveSource.restrict U).withDensity jacobianDensity).restrict V :=
        hrestrict_eq
      _ ≤ (ENNReal.ofReal K • passiveSource.restrict U).restrict V :=
        hweighted_restrict
      _ = ENNReal.ofReal K • passiveSource.restrict V := by
        rw [Measure.restrict_smul]
        rw [Measure.restrict_restrict_of_subset hVU]
  have hmap_base :
      Measure.map rawMap (baseJ.restrict V) ≤
        ENNReal.ofReal K • Measure.map rawMap (passiveSource.restrict V) :=
    map_le_smul_map_of_le_smul_aemeasurable hrawMap hbase_dom
  have hmap_source :
      Measure.map rawMap (passiveSource.restrict V) ≤
        c • ((rawHaar.restrict rawSourceSet).withDensity
          rawInverseJacobianDensity) :=
    hraw_dom rawHaar hYdom
  exact measure_le_smul_of_le_smul_of_le_smul hmap_base hmap_source

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
