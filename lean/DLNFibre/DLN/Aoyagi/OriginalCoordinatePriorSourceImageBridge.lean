import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyRawOrderMeasureBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination

/-!
# Original coordinate priors at the source-image domination interface

This file exposes the existing conditional source-image domination theorem on
the original flattened-coordinate side.  The only new step is the
finite-dimensional coordinate-to-edge-family prior transport restricted to the
preimage of the returned source-chart image.

It does not construct source-image densities, identify chart-produced source
measures with Aoyagi's prior, prove determinant/raw Haar transport, normalize
Haar scalars, prove source-rank coverage, construct normal crossings, compute
pole order, or extract RLCT.
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

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper elaborates the large Case 2 source-image domination package.
/-- Source-image domination restated for pushed original coordinate priors.

The existing source-image theorem dominates the original edge-family prior on
`sourceChart '' V`.  Here the edge density is the pullback of a flattened
coordinate density through the fixed-basis edge-family coordinates, and the
left side is rewritten as the pushforward of the original coordinate prior
restricted to the preimage of the same chart image.

The determinant-side domination, the lower source-density bound, the local
prior-density upper bound, and the tuple-side a.e.-measurability needed for
transport remain explicit hypotheses. -/
theorem exists_open_subset_map_originalCoordinatePrior_restrict_sourceChart_preimage_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceImageDensity_comp_sourceChart_lower_priorDensity_comp_sourceChart_upper
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
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
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
    {ε : ℝ≥0∞}
    (coordDensity : (RepCoord (paperEndpointFixedBaseDim W₂ B₂ U₀) → ℝ) → ℝ)
    {Kprior : ℝ} :
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
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let b := paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀
    let toEdge : (RepCoord d → ℝ) → EdgeFamily :=
      fun x ↦ tupleToEdgeFamily (V := reverseVertex W₂) b ((canonicalCoord d).symm x)
    let edgeDensity : EdgeFamily → ℝ :=
      fun E ↦ coordDensity
        (canonicalCoord d (edgeFamilyMatrixTuple (V := reverseVertex W₂) b E))
    (∀ᶠ z in nhds z₀, ε ≤ sourceImageDensity (sourceChart z)) →
      (∀ᶠ z in nhds z₀, edgeDensity (sourceChart z) ≤ Kprior) →
        ∃ V :
          Set
            (Case2PassiveTheta
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
          IsOpen V ∧ z₀ ∈ V ∧
            (∀ z ∈ V, readback (sourceChart z) = z) ∧
              Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                MeasurableSet (sourceChart '' V) ∧
                  (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                    ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                    ∀ {Cdet : ℝ≥0∞},
                      rawHaar.restrict rawDetChart ≤
                        Cdet • Measure.map Y (passiveSource.restrict V) →
                        Cdet < ∞ →
                          ε ≠ 0 →
                            ε ≠ ∞ →
                              AEMeasurable
                                (fun A : Tuple (k := ℝ) d ↦
                                  ENNReal.ofReal (coordDensity (canonicalCoord d A)))
                                ((originalTupleVolume d).restrict
                                  ((tupleToEdgeFamily (V := reverseVertex W₂) b) ⁻¹'
                                    (sourceChart '' V))) →
                                let cHaar :=
                                  ((Measure.map
                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                      W₂ B₂ U₀)
                                    rawHaar).addHaarScalarFactor (originalTupleVolume d))
                                let Ddet := Cdet * ε⁻¹
                                let Dvol := ((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet
                                let Cprior := ENNReal.ofReal Kprior * Dvol
                                Cprior < ∞ ∧
                                  Measure.map toEdge
                                    ((originalCoordinatePrior d coordDensity).restrict
                                      (toEdge ⁻¹' (sourceChart '' V))) ≤
                                    Cprior •
                                      (Measure.map sourceChart
                                        (coordinateSourceMeasure.restrict V)).restrict
                                          (sourceChart '' V) := by
  intro center pivotNext signedBox weightedBox passiveSource RawTuple EdgeFamily
    Y rawMap jacobianDensity baseJ sourceChart readback sourceDensity
    coordinateSourceMeasure rawDetChart rawSourceSet p13SourceSet d b toEdge
    edgeDensity hsource_eventually hprior_eventually
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, EdgeFamily, Y, rawMap, jacobianDensity, baseJ,
          sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawDetChart, rawSourceSet, p13SourceSet, d, edgeDensity] using
          exists_open_subset_originalEdgeFamilyPrior_restrict_sourceChart_image_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceImageDensity_comp_sourceChart_lower_priorDensity_comp_sourceChart_upper
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres
            (ε := ε) (density := edgeDensity) (Kprior := Kprior)
            hsource_eventually hprior_eventually) with
    ⟨V, hVopen, hz₀V, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, hprior_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V' : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  refine ⟨V, hVopen, hz₀V, hleftV', hsource_injV, hsource_contOnV,
    hsource_imageV, himage_p13V', ?_⟩
  intro rawHaar _instRawHaar Cdet hdet_dom hCdet hε_ne_zero hε_ne_top
    hdensity cHaar Ddet Dvol Cprior
  have hedge_package :
      Cprior < ∞ ∧
        (originalEdgeFamilyPrior (V := reverseVertex W₂)
          b edgeDensity).restrict (sourceChart '' V) ≤
            Cprior •
              (Measure.map sourceChart
                (coordinateSourceMeasure.restrict V)).restrict
                  (sourceChart '' V) := by
    simpa [cHaar, Ddet, Dvol, Cprior, b, d, edgeDensity] using
      hprior_package rawHaar hdet_dom hCdet hε_ne_zero hε_ne_top
  have htransport :
      Measure.map toEdge
          ((originalCoordinatePrior d coordDensity).restrict
            (toEdge ⁻¹' (sourceChart '' V))) =
        (originalEdgeFamilyPrior (V := reverseVertex W₂)
          b edgeDensity).restrict (sourceChart '' V) := by
    simpa [toEdge, b, d, edgeDensity] using
      map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_preimage_eq_originalEdgeFamilyPrior_restrict
        (V := reverseVertex W₂) (d := d) b
        (density := coordDensity) (Cset := sourceChart '' V)
        hsource_imageV hdensity
  refine ⟨hedge_package.1, ?_⟩
  calc
    Measure.map toEdge
        ((originalCoordinatePrior d coordDensity).restrict
          (toEdge ⁻¹' (sourceChart '' V))) =
        (originalEdgeFamilyPrior (V := reverseVertex W₂)
          b edgeDensity).restrict (sourceChart '' V) := htransport
    _ ≤
        Cprior •
          (Measure.map sourceChart
            (coordinateSourceMeasure.restrict V)).restrict
              (sourceChart '' V) := hedge_package.2

end PaperEndpointFixedBaseRegularCoordinateSourceData
end Aoyagi
end DLN
end DLNFibre

end
