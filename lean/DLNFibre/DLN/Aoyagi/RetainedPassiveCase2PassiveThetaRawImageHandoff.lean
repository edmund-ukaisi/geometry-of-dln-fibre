import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobianMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure

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
