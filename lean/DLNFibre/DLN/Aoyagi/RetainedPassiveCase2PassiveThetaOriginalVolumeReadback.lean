import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeBridge
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13ReadbackFiniteIntegral

/-!
# Case 2 passive-theta original-volume readback bridge

This file composes the conditional Case 2 passive-theta original-volume
source-image bridge with the p.13 source-chart readback-domination adapter.

The raw-Haar raw-source pushforward remains an explicit hypothesis.  The result
only packages readback a.e. measurability and domination on the same local
shrink; it does not prove Haar transport, source coverage, normal crossings, or
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

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The unfolded with-following chart package creates a large dependent statement.
/-- Same-shrink with-following inverse-Haar density and readback bridge.

Under the exact local raw-pushforward identity, every measurable chart piece
inside the actual local with-following source image has both the exact
constant inverse-Haar source-image density identity for restricted original
edge-family volume and the induced readback domination by the same inverse
Haar scalar.

The raw-pushforward identity remains a hypothesis.  This theorem does not
prove determinant-chart Haar transport, raw-order Haar transport, source-prior
transport, source-image coverage, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_and_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
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
                            invHaarDensity E ≤ ((c⁻¹ : NNReal) : ℝ≥0∞)) ∧
                            AEMeasurable readback
                              (originalVolume.restrict chartPiece) ∧
                              Measure.map readback
                                  (originalVolume.restrict chartPiece) ≤
                                (((c⁻¹ : NNReal) : ℝ≥0∞) •
                                  thetaReference.restrict G) := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawSourceSet
    p13SourceSet d originalVolume
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, readback, rawMap,
          rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hbridge⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ V := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ V := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hzV
    simpa [sourceChart, p13SourceSet,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.1.A1passive z.1.F2 z.1.A3passive
        z.1.Ctop z.1.F3 z.1.yNext z.2 hz_fields rfl
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_contOn,
      hsource_image, himage_p13V, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_image hraw_push c sourceRef invHaarDensity
  have hbridge_piece :
      originalVolume.restrict chartPiece =
          (sourceRef.withDensity invHaarDensity).restrict chartPiece ∧
        (∀ᵐ E ∂sourceRef.restrict chartPiece,
          invHaarDensity E ≤ ((c⁻¹ : NNReal) : ℝ≥0∞)) := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
      p13SourceSet, d, originalVolume, c, sourceRef, invHaarDensity] using
      hbridge thetaReference rawHaar chartPiece hchartPiece
        hchartPiece_image hraw_push
  have hread :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          (((c⁻¹ : NNReal) : ℝ≥0∞) • thetaReference.restrict G) := by
    simpa [RawTuple, EdgeFamily, sourceRef, invHaarDensity] using
      originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_withDensity_of_continuousOn_injOn
        (W₂ := W₂) (B₂ := B₂) (U₀ := U₀) (hU₀ := hU₀)
        sourceChart readback thetaReference V G chartPiece invHaarDensity
        (((c⁻¹ : NNReal) : ℝ≥0∞))
        hVopen.measurableSet hchartPiece hVG hsource_contOn hsource_inj hleftV
        hbridge_piece.1 hbridge_piece.2
  exact ⟨hbridge_piece.1, hbridge_piece.2, hread⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Conditional same-shrink readback domination for the original edge-family
volume on the concrete Case 2 passive-theta source image.

If the local passive-theta raw-order map pushes `thetaReference.restrict V`
exactly to the raw-order source-recursive restriction of a raw Haar measure,
then every measurable chart piece inside the actual local image
`sourceChart '' V` has a.e.-measurable readback and readback pushforward
dominated by the inverse Haar scalar times `thetaReference.restrict G`.

The raw-pushforward identity is a hypothesis.  This theorem does not prove
determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
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
                        let D : ℝ≥0∞ := ((c⁻¹ : NNReal) : ℝ≥0∞)
                        AEMeasurable readback (originalVolume.restrict chartPiece) ∧
                          Measure.map readback (originalVolume.restrict chartPiece) ≤
                            D • thetaReference.restrict G := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawSourceSet
    p13SourceSet d originalVolume
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, readback, rawMap,
          rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hbridge⟩
  refine
    ⟨V, hVopen, hz₀V, hVG, ?_, hsource_inj, hsource_contOn,
      hsource_image, ?_, ?_⟩
  · intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  · intro E hE
    rcases hE with ⟨z, hz, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.A1passive z.F2 z.A3passive z.Ctop
        z.F3 z.yNext hz rfl
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_sub_image hraw_push c D
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  let invHaarDensity : EdgeFamily → ℝ≥0∞ := fun _ ↦ D
  have hbridge_piece :
      originalVolume.restrict chartPiece =
          ((Measure.map sourceChart (thetaReference.restrict V)).withDensity
            invHaarDensity).restrict chartPiece ∧
        (∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict
          chartPiece, invHaarDensity E ≤ D) := by
    simpa [c, D, invHaarDensity] using
      hbridge thetaReference rawHaar chartPiece hchartPiece
        hchartPiece_sub_image hraw_push
  have hread :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          D • thetaReference.restrict G := by
    simpa [originalVolume, invHaarDensity] using
      originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_withDensity_of_continuousOn_injOn
        (W₂ := W₂) (B₂ := B₂) (U₀ := U₀) (hU₀ := hU₀)
        sourceChart readback thetaReference V G chartPiece invHaarDensity D
        hVopen.measurableSet hchartPiece hVG hsource_contOn hsource_inj hleftV
        hbridge_piece.1 hbridge_piece.2
  exact hread

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete theorem composes two large Case 2 local packages and then unfolds their chart notation.
/-- Conditional same-shrink readback domination from reverse raw-source
domination.

If raw Haar restricted to the raw-order source-recursive chart is dominated by
a scalar multiple of the local passive-theta raw-order image, then on a smaller
local source-chart image every measurable chart piece has a.e.-measurable
original-volume readback, and its readback pushforward is dominated by the
inverse Haar scalar times that raw-domination scalar.

The reverse raw-source domination is a hypothesis.  This theorem does not prove
determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
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
                ∀ {D : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      rawHaar.restrict rawSourceSet ≤
                        D • Measure.map rawMap (thetaReference.restrict V) →
                        let c :=
                          ((Measure.map
                            (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                              W₂ B₂ U₀)
                            rawHaar).addHaarScalarFactor (originalTupleVolume d))
                        AEMeasurable readback (originalVolume.restrict chartPiece) ∧
                          Measure.map readback (originalVolume.restrict chartPiece) ≤
                            ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) •
                              thetaReference.restrict G) := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawSourceSet
    p13SourceSet d originalVolume
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback, p13SourceSet] using
          exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V₀, hV₀open, hz₀V₀, hV₀G, _hdetV₀, hleft₀, hsource_inj₀,
      hsource_contOn₀, _hsource_image₀, _hpoint₀, himage_p13₀⟩
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
          p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ V₀ hV₀open hz₀V₀) with
    ⟨V, hVopen, hz₀V, hVV₀, hvolume_bridge⟩
  have hVG : V ⊆ G := fun z hz ↦ hV₀G (hVV₀ hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz₀_fields :
        ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈
          V₀ := by
      simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hVV₀ hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft₀ z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext
        hz₀_fields
  have hsource_injV : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    exact hsource_inj₀ (hVV₀ hz) (hVV₀ hz') hsrc
  have hsource_contOnV : ContinuousOn sourceChart V :=
    hsource_contOn₀.mono hVV₀
  have hsource_imageV : MeasurableSet (sourceChart '' V) :=
    hVopen.measurableSet.image_of_continuousOn_injOn hsource_contOnV hsource_injV
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    have hz₀_fields :
        ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈
          V₀ := by
      simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hVV₀ hzV
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13₀ (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hz₀_fields rfl
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece D hchartPiece
    hchartPiece_sub_image hraw_dom c
  let sourceRef : Measure EdgeFamily :=
    Measure.map sourceChart (thetaReference.restrict V)
  let Cvol : ℝ≥0∞ := (((c⁻¹ : NNReal) : ℝ≥0∞) * D)
  have hchartPiece_sub_p13 : chartPiece ⊆ p13SourceSet := by
    intro E hE
    exact himage_p13V E (hchartPiece_sub_image hE)
  have hvolume_dom :
      originalVolume.restrict chartPiece ≤ Cvol • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
      p13SourceSet, d, originalVolume, sourceRef, c, Cvol] using
      hvolume_bridge thetaReference rawHaar chartPiece (D := D) hchartPiece
        hchartPiece_sub_p13 hraw_dom
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hsource_aemeas :
      AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOnV.aemeasurable hVmeas
  have hreadback_source : AEMeasurable readback sourceRef := by
    simpa [sourceRef] using
      aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
        sourceChart readback thetaReference V hVmeas hsource_contOnV
        hsource_injV hleftV
  have hsource_pull_eq :
      Measure.map readback sourceRef = thetaReference.restrict V := by
    simpa [sourceRef] using
      measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
        sourceChart readback thetaReference V hVmeas hsource_aemeas
        hreadback_source hleftV
  have hrestrict_le :
      thetaReference.restrict V ≤ thetaReference.restrict G :=
    Measure.restrict_mono hVG le_rfl
  have hsource_pull_le :
      Measure.map readback sourceRef ≤
        (1 : ℝ≥0∞) • thetaReference.restrict G := by
    simpa [hsource_pull_eq] using hrestrict_le
  have hread :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          Cvol • thetaReference.restrict G := by
    simpa [Cvol, one_mul, mul_one] using
      readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
        (sourceRef := sourceRef) (μ := originalVolume.restrict chartPiece)
        (thetaRef := thetaReference.restrict G) (C := Cvol)
        (Csource := (1 : ℝ≥0∞)) (readback := readback)
        hreadback_source hsource_pull_le hvolume_dom
  simpa [RawTuple, EdgeFamily, d, originalVolume, c, Cvol] using hread

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Localized with-following readback domination from a chart-piece raw patch.
/-- Conditional same-shrink readback domination for the original edge-family
volume on the enlarged source-image chart pieces, from localized reverse
raw-source domination.

If raw Haar restricted to a raw patch `P` is dominated by a scalar multiple of
the local enlarged passive-theta raw-order image, and `P` contains the raw
preimage of the selected p.13 chart piece inside the raw source set, then on a
smaller local source-chart image that chart piece has a.e.-measurable
original-volume readback, and its readback pushforward is dominated by the
inverse Haar scalar times the raw-domination scalar.

The localized reverse raw-source domination is a hypothesis.  This theorem
does not prove determinant-chart Haar transport, raw-order Haar transport,
original source-prior transport, source-image coverage, source-rank coverage,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_patch_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
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
                ∀ P : Set RawTuple,
                ∀ {D : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      P ⊆ rawSourceSet →
                        rawSourceSet ∩ rawChart ⁻¹' chartPiece ⊆ P →
                          rawHaar.restrict P ≤
                            D • Measure.map rawMap (thetaReference.restrict V) →
                          let c :=
                            ((Measure.map
                              (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                W₂ B₂ U₀)
                              rawHaar).addHaarScalarFactor (originalTupleVolume d))
                          AEMeasurable readback (originalVolume.restrict chartPiece) ∧
                            Measure.map readback (originalVolume.restrict chartPiece) ≤
                              ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) •
                                thetaReference.restrict G) := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawSourceSet
    p13SourceSet rawChart d originalVolume
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback, p13SourceSet] using
          exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V₀, hV₀open, hz₀V₀, hV₀G, _hdetV₀, hleft₀, hsource_inj₀,
      hsource_contOn₀, _hsource_image₀, hpoint₀, _himage_p13₀⟩
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
          p13SourceSet, rawChart, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_patch_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ V₀ hV₀open hz₀V₀) with
    ⟨V, hVopen, hz₀V, hVV₀, hvolume_bridge⟩
  have hVG : V ⊆ G := fun z hz ↦ hV₀G (hVV₀ hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ V₀ := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hVV₀ hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft₀ z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 (hVV₀ hz)
  have hsource_injV : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    exact hsource_inj₀ (hVV₀ hz) (hVV₀ hz') hsrc
  have hsource_contOnV : ContinuousOn sourceChart V :=
    hsource_contOn₀.mono hVV₀
  have hsource_imageV : MeasurableSet (sourceChart '' V) :=
    hVopen.measurableSet.image_of_continuousOn_injOn hsource_contOnV hsource_injV
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
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece P D hchartPiece
    hchartPiece_sub_image hP_sub hrawPatch_sub hraw_dom c
  let sourceRef : Measure EdgeFamily :=
    Measure.map sourceChart (thetaReference.restrict V)
  let Cvol : ℝ≥0∞ := (((c⁻¹ : NNReal) : ℝ≥0∞) * D)
  have hchartPiece_sub_p13 : chartPiece ⊆ p13SourceSet := by
    intro E hE
    exact himage_p13V E (hchartPiece_sub_image hE)
  have hvolume_dom :
      originalVolume.restrict chartPiece ≤ Cvol • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
      p13SourceSet, rawChart, d, originalVolume, sourceRef, c, Cvol] using
      hvolume_bridge thetaReference rawHaar chartPiece P (D := D) hchartPiece
        hchartPiece_sub_p13 hP_sub hrawPatch_sub hraw_dom
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hsource_aemeas :
      AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOnV.aemeasurable hVmeas
  have hreadback_source : AEMeasurable readback sourceRef := by
    simpa [sourceRef] using
      aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
        sourceChart readback thetaReference V hVmeas hsource_contOnV
        hsource_injV hleftV
  have hsource_pull_eq :
      Measure.map readback sourceRef = thetaReference.restrict V := by
    simpa [sourceRef] using
      measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
        sourceChart readback thetaReference V hVmeas hsource_aemeas
        hreadback_source hleftV
  have hrestrict_le :
      thetaReference.restrict V ≤ thetaReference.restrict G :=
    Measure.restrict_mono hVG le_rfl
  have hsource_pull_le :
      Measure.map readback sourceRef ≤
        (1 : ℝ≥0∞) • thetaReference.restrict G := by
    simpa [hsource_pull_eq] using hrestrict_le
  have hread :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          Cvol • thetaReference.restrict G := by
    simpa [Cvol, one_mul, mul_one] using
      readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
        (sourceRef := sourceRef) (μ := originalVolume.restrict chartPiece)
        (thetaRef := thetaReference.restrict G) (C := Cvol)
        (Csource := (1 : ℝ≥0∞)) (readback := readback)
        hreadback_source hsource_pull_le hvolume_dom
  simpa [RawTuple, EdgeFamily, d, originalVolume, c, Cvol] using hread

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The concrete theorem composes the with-following source chart with original-volume domination.
/-- Conditional same-shrink readback domination for the original edge-family
volume on the enlarged Case 2 passive-theta source image.

If the enlarged passive-theta raw-order map pushes `thetaReference.restrict V`
exactly to the raw-order source-recursive restriction of a raw Haar measure,
then every measurable p.13 chart piece inside the actual local image
`sourceChart '' V` has a.e.-measurable readback and readback pushforward
dominated by the inverse Haar scalar times `thetaReference.restrict G`.

The raw-pushforward identity and p.13 chart-piece containment are hypotheses.
This theorem does not prove determinant-chart Haar transport, raw-order Haar
transport, original source-prior transport, source-image coverage, source-rank
coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
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
                          let c :=
                            ((Measure.map
                              (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                W₂ B₂ U₀)
                              rawHaar).addHaarScalarFactor (originalTupleVolume d))
                          let D : ℝ≥0∞ := ((c⁻¹ : NNReal) : ℝ≥0∞) * (1 : ℝ≥0∞)
                          AEMeasurable readback (originalVolume.restrict chartPiece) ∧
                            Measure.map readback (originalVolume.restrict chartPiece) ≤
                              D • thetaReference.restrict G := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawSourceSet
    p13SourceSet d originalVolume
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback] using
          exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V₀, hV₀open, hz₀V₀, hV₀G, _hdetV₀, hleft₀, hsource_inj₀,
      hsource_contOn₀, _hsource_image₀⟩
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
          p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ V₀ hV₀open hz₀V₀) with
    ⟨V, hVopen, hz₀V, hVV₀, hvolume_bridge⟩
  have hVG : V ⊆ G := fun z hz ↦ hV₀G (hVV₀ hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz₀_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ V₀ := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hVV₀ hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft₀ z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz₀_fields
  have hsource_injV : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    exact hsource_inj₀ (hVV₀ hz) (hVV₀ hz') hsrc
  have hsource_contOnV : ContinuousOn sourceChart V :=
    hsource_contOn₀.mono hVV₀
  have hsource_imageV : MeasurableSet (sourceChart '' V) :=
    hVopen.measurableSet.image_of_continuousOn_injOn hsource_contOnV hsource_injV
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_sub_image hchartPiece_p13 hraw_push c D
  let sourceRef : Measure EdgeFamily :=
    Measure.map sourceChart (thetaReference.restrict V)
  have hvolume_dom :
      originalVolume.restrict chartPiece ≤ D • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
      p13SourceSet, d, originalVolume, sourceRef, c, D] using
      hvolume_bridge thetaReference rawHaar chartPiece hchartPiece
        hchartPiece_sub_image hchartPiece_p13 hraw_push
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hsource_aemeas :
      AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOnV.aemeasurable hVmeas
  have hreadback_source : AEMeasurable readback sourceRef := by
    simpa [sourceRef] using
      aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
        sourceChart readback thetaReference V hVmeas hsource_contOnV
        hsource_injV hleftV
  have hsource_pull_eq :
      Measure.map readback sourceRef = thetaReference.restrict V := by
    simpa [sourceRef] using
      measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
        sourceChart readback thetaReference V hVmeas hsource_aemeas
        hreadback_source hleftV
  have hrestrict_le :
      thetaReference.restrict V ≤ thetaReference.restrict G :=
    Measure.restrict_mono hVG le_rfl
  have hsource_pull_le :
      Measure.map readback sourceRef ≤
        (1 : ℝ≥0∞) • thetaReference.restrict G := by
    simpa [hsource_pull_eq] using hrestrict_le
  have hread :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          D • thetaReference.restrict G := by
    simpa [mul_one] using
      readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
        (sourceRef := sourceRef) (μ := originalVolume.restrict chartPiece)
        (thetaRef := thetaReference.restrict G) (C := D)
        (Csource := (1 : ℝ≥0∞)) (readback := readback)
        hreadback_source hsource_pull_le hvolume_dom
  simpa [RawTuple, EdgeFamily, d, originalVolume, c, D] using hread

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper discharges p.13 support from local source-image support.
/-- Conditional same-shrink readback domination for the original edge-family
volume on enlarged source-image chart pieces, with p.13 support discharged.

If the enlarged passive-theta raw-order map pushes `thetaReference.restrict V`
exactly to the raw-order source-recursive restriction of a raw Haar measure,
then every measurable chart piece inside the actual local image
`sourceChart '' V` has a.e.-measurable readback and readback pushforward
dominated by the inverse Haar scalar times `thetaReference.restrict G`.

The raw-pushforward identity, chart-piece measurability, and source-image
membership are hypotheses.  The p.13 chart-piece containment is derived from
local source-image support.  This theorem does not prove determinant-chart Haar
transport, raw-order Haar transport, original source-prior transport,
source-image coverage, source-rank coverage, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource_of_chartPiece_subset_sourceImage
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
                          let D : ℝ≥0∞ := ((c⁻¹ : NNReal) : ℝ≥0∞) * (1 : ℝ≥0∞)
                          AEMeasurable readback (originalVolume.restrict chartPiece) ∧
                            Measure.map readback (originalVolume.restrict chartPiece) ≤
                              D • thetaReference.restrict G := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawSourceSet
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
        simpa [RawTuple, EdgeFamily, sourceChart, readback, rawMap,
          rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ V₀ hV₀open hz₀V₀) with
    ⟨V, hVopen, hz₀V, hVV₀, hleft, hsource_inj, hsource_contOn,
      hsource_image, hreadback_bridge⟩
  have hVG : V ⊆ G := fun z hz ↦ hV₀G (hVV₀ hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ V := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
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
    hchartPiece_image hraw_push c D
  have hchartPiece_p13 : chartPiece ⊆ p13SourceSet := by
    intro E hE
    exact himage_p13V E (hchartPiece_image hE)
  have hreadback_step :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          D • thetaReference.restrict V₀ := by
    simpa [RawTuple, EdgeFamily, d, originalVolume, c, D] using
      hreadback_bridge thetaReference rawHaar chartPiece hchartPiece
        hchartPiece_image hchartPiece_p13 hraw_push
  have hV₀_le_G :
      thetaReference.restrict V₀ ≤
        (1 : ℝ≥0∞) • thetaReference.restrict G := by
    simpa using (Measure.restrict_mono hV₀G le_rfl)
  have hmap_le_G :
      Measure.map readback (originalVolume.restrict chartPiece) ≤
        D • thetaReference.restrict G := by
    have hstep :
        Measure.map readback (originalVolume.restrict chartPiece) ≤
        (D * (1 : ℝ≥0∞)) • thetaReference.restrict G :=
      measure_le_smul_of_le_smul_of_le_smul hreadback_step.2 hV₀_le_G
    simpa [mul_one] using hstep
  exact ⟨hreadback_step.1, hmap_le_G⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This is the p.13/readback-preimage support form of the with-following readback bridge.
/-- Conditional same-shrink readback domination for original edge-family volume
on enlarged p.13/readback-preimage chart pieces.

The local with-following image equality converts the caller's
`chartPiece ⊆ p13SourceSet` and `chartPiece ⊆ readback ⁻¹' V` hypotheses into
the actual source-image containment consumed by the existing readback bridge.

The raw-pushforward identity remains a hypothesis.  This theorem does not
prove determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource_of_chartPiece_subset_p13SourceSet_readback_preimage
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
              sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                ∀ thetaReference :
                  Measure
                    (Case2PassiveThetaWithFollowingFactor
                      (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                  ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                  ∀ chartPiece : Set EdgeFamily,
                    MeasurableSet chartPiece →
                      chartPiece ⊆ p13SourceSet →
                        chartPiece ⊆ readback ⁻¹' V →
                          Measure.map rawMap (thetaReference.restrict V) =
                            rawHaar.restrict rawSourceSet →
                            let c :=
                              ((Measure.map
                                (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                  W₂ B₂ U₀)
                                rawHaar).addHaarScalarFactor (originalTupleVolume d))
                            let D : ℝ≥0∞ := ((c⁻¹ : NNReal) : ℝ≥0∞) * (1 : ℝ≥0∞)
                            AEMeasurable readback (originalVolume.restrict chartPiece) ∧
                              Measure.map readback (originalVolume.restrict chartPiece) ≤
                                D • thetaReference.restrict G := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawSourceSet
    p13SourceSet d originalVolume
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback, p13SourceSet] using
          exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_eq_p13SourceEdgeFamilySet_inter_readback_preimage
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨W, hWopen, hz₀W, hWG, _hdetW, _hpivotW, hleftW, _hsource_injW,
      _hsource_contOnW, _hsource_imageW, himageW⟩
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, readback, rawMap,
          rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ W hWopen hz₀W) with
    ⟨V, hVopen, hz₀V, hVW, hleft, hsource_inj, hsource_contOn,
      hsource_image, hreadback_bridge⟩
  have hVG : V ⊆ G := fun z hz ↦ hWG (hVW hz)
  have hleftW' : ∀ z ∈ W, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ W := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftW z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ V := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  have himageV : sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V :=
    sourceChart_image_eq_p13_readback_preimage_of_subset
      (sourceChart := sourceChart) (readback := readback)
      (V := V) (W := W) (p13SourceSet := p13SourceSet)
      himageW hVW hleftW'
  refine
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_inj, hsource_contOn,
      hsource_image, himageV, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_p13 hchartPiece_readback hraw_push c D
  have hchartPiece_image : chartPiece ⊆ sourceChart '' V :=
    chartPiece_subset_sourceChart_image_of_subset_p13_readback
      (sourceChart := sourceChart) (readback := readback)
      (V := V) (p13SourceSet := p13SourceSet)
      (chartPiece := chartPiece) himageV hchartPiece_p13 hchartPiece_readback
  have hreadback_step :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          D • thetaReference.restrict W := by
    simpa [RawTuple, EdgeFamily, d, originalVolume, c, D] using
      hreadback_bridge thetaReference rawHaar chartPiece hchartPiece
        hchartPiece_image hchartPiece_p13 hraw_push
  have hW_le_G :
      thetaReference.restrict W ≤
        (1 : ℝ≥0∞) • thetaReference.restrict G := by
    simpa using (Measure.restrict_mono hWG le_rfl)
  have hmap_le_G :
      Measure.map readback (originalVolume.restrict chartPiece) ≤
        D • thetaReference.restrict G := by
    have hstep :
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          (D * (1 : ℝ≥0∞)) • thetaReference.restrict G :=
      measure_le_smul_of_le_smul_of_le_smul hreadback_step.2 hW_le_G
    simpa [mul_one] using hstep
  exact ⟨hreadback_step.1, hmap_le_G⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This is the with-following reverse-raw-domination analogue of the
-- non-following readback bridge above.
/-- Conditional same-shrink readback domination for the original edge-family
volume on the enlarged source-image chart pieces, from reverse raw-source
domination.

If raw Haar restricted to the raw-order source-recursive chart is dominated by
a scalar multiple of the local enlarged passive-theta raw-order image, then on
a smaller local source-chart image every measurable chart piece has
a.e.-measurable original-volume readback, and its readback pushforward is
dominated by the inverse Haar scalar times that raw-domination scalar.

The reverse raw-source domination is a hypothesis.  This theorem does not
prove determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
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
                ∀ {D : ℝ≥0∞},
                  MeasurableSet chartPiece →
                    chartPiece ⊆ sourceChart '' V →
                      rawHaar.restrict rawSourceSet ≤
                        D • Measure.map rawMap (thetaReference.restrict V) →
                        let c :=
                          ((Measure.map
                            (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                              W₂ B₂ U₀)
                            rawHaar).addHaarScalarFactor (originalTupleVolume d))
                        AEMeasurable readback (originalVolume.restrict chartPiece) ∧
                          Measure.map readback (originalVolume.restrict chartPiece) ≤
                            ((((c⁻¹ : NNReal) : ℝ≥0∞) * D) •
                              thetaReference.restrict G) := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawSourceSet
    p13SourceSet d originalVolume
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback, p13SourceSet] using
          exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨V₀, hV₀open, hz₀V₀, hV₀G, _hdetV₀, hleft₀, hsource_inj₀,
      hsource_contOn₀, _hsource_image₀, hpoint₀, _himage_p13₀⟩
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
          p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ V₀ hV₀open hz₀V₀) with
    ⟨V, hVopen, hz₀V, hVV₀, hvolume_bridge⟩
  have hVG : V ⊆ G := fun z hz ↦ hV₀G (hVV₀ hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ V₀ := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hVV₀ hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft₀ z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 (hVV₀ hz)
  have hsource_injV : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    exact hsource_inj₀ (hVV₀ hz) (hVV₀ hz') hsrc
  have hsource_contOnV : ContinuousOn sourceChart V :=
    hsource_contOn₀.mono hVV₀
  have hsource_imageV : MeasurableSet (sourceChart '' V) :=
    hVopen.measurableSet.image_of_continuousOn_injOn hsource_contOnV hsource_injV
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
    ⟨V, hVopen, hz₀V, hVG, hleftV, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece D hchartPiece
    hchartPiece_sub_image hraw_dom c
  let sourceRef : Measure EdgeFamily :=
    Measure.map sourceChart (thetaReference.restrict V)
  let Cvol : ℝ≥0∞ := (((c⁻¹ : NNReal) : ℝ≥0∞) * D)
  have hchartPiece_sub_p13 : chartPiece ⊆ p13SourceSet := by
    intro E hE
    exact himage_p13V E (hchartPiece_sub_image hE)
  have hvolume_dom :
      originalVolume.restrict chartPiece ≤ Cvol • sourceRef := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawSourceSet,
      p13SourceSet, d, originalVolume, sourceRef, c, Cvol] using
      hvolume_bridge thetaReference rawHaar chartPiece (D := D) hchartPiece
        hchartPiece_sub_p13 hraw_dom
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hsource_aemeas :
      AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOnV.aemeasurable hVmeas
  have hreadback_source : AEMeasurable readback sourceRef := by
    simpa [sourceRef] using
      aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
        sourceChart readback thetaReference V hVmeas hsource_contOnV
        hsource_injV hleftV
  have hsource_pull_eq :
      Measure.map readback sourceRef = thetaReference.restrict V := by
    simpa [sourceRef] using
      measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
        sourceChart readback thetaReference V hVmeas hsource_aemeas
        hreadback_source hleftV
  have hrestrict_le :
      thetaReference.restrict V ≤ thetaReference.restrict G :=
    Measure.restrict_mono hVG le_rfl
  have hsource_pull_le :
      Measure.map readback sourceRef ≤
        (1 : ℝ≥0∞) • thetaReference.restrict G := by
    simpa [hsource_pull_eq] using hrestrict_le
  have hread :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          Cvol • thetaReference.restrict G := by
    simpa [Cvol, one_mul, mul_one] using
      readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
        (sourceRef := sourceRef) (μ := originalVolume.restrict chartPiece)
        (thetaRef := thetaReference.restrict G) (C := Cvol)
        (Csource := (1 : ℝ≥0∞)) (readback := readback)
        hreadback_source hsource_pull_le hvolume_dom
  simpa [RawTuple, EdgeFamily, d, originalVolume, c, Cvol] using hread

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- Original edge-family priors feed into the Case 2 finite-integral socket
from the same-shrink conditional raw-Haar source pushforward hypothesis.

The theorem uses the direct original-volume readback finite-integral front end,
then discharges its readback a.e.-measurability and domination hypotheses by
the same local `V` supplied by the conditional original-volume/source-image
readback bridge.

The raw-pushforward identity is still a chart-piece hypothesis.  This theorem
does not prove determinant-chart Haar transport, raw-order Haar transport,
original source-prior transport, source-image coverage, source-rank coverage,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_case2PassiveTheta_rawMap_eq_restrict_rawSource_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure] [SFinite ν]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
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
    let passiveSource := passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
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
    let baseJ := passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
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
    let rawDetChart :
        Set (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet :
        Set (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let p13SourceChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let cHaar :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W₂ B₂ U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    ∃ V : Set
                      (Case2PassiveTheta
                        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
                        (∀ z ∈ V, readback (sourceChart z) = z) ∧
                        Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                        MeasurableSet (sourceChart '' V) ∧
                        (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                    let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                    MeasurableSet sourceLocal ∧
                      ∀ {chartPiece : Set EdgeFamily},
                        MeasurableSet chartPiece →
                          chartPiece ⊆ sourceLocal →
                            chartPiece ⊆ sourceChart '' V →
                              Measure.map rawMap (coordinateSourceMeasure.restrict V) =
                                m.restrict rawSourceSet →
                                ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                  (∀ᵐ E ∂(originalEdgeFamilyVolume
                                    (V := reverseVertex W₂)
                                    (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)).restrict
                                      chartPiece,
                                      density E ≤ Kprior) →
                                              (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                                ENNReal.ofReal
                                                  ((Metric.ball
                                                    (0 : EuclideanSpace ℝ ρreg) R).indicator
                                                    (fun u ↦
                                                      (loss (z.1, u)) ^
                                                        (-(t +
                                                          (aoyagiTheorem2RegularVariableCount
                                                              2 H r : ℝ) /
                                                            2))) z.2) ∂
                                                ((originalEdgeFamilyPrior (V := reverseVertex W₂)
                                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                  density).restrict chartPiece).prod ν) <
                                                  ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y rawMap
    jacobianDensity baseJ EdgeFamily sourceChart readback sourceDensity
    coordinateSourceMeasure base ρreg sourceStratum rawDetChart rawSourceSet
    p13SourceSet p13SourceChart d originalVolume cHaar hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, base, ρreg, sourceStratum,
          rawDetChart, p13SourceChart, d, cHaar] using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top m Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  have hsourceChart' :
      AEMeasurable
        (case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W) := by
    simpa [sourceChart, baseJ, passiveSource] using hsourceChart
  have hsourceImageDensity' :
      AEMeasurable sourceImageDensity
        (Measure.map
          (case2PassiveThetaEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
          (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W)) := by
    simpa [sourceImageBase, sourceChart, baseJ, passiveSource] using
      hsourceImageDensity
  rcases
      hsocket hsourceChart' hsourceImageDensity'
        (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, hfinite⟩
  rcases
      (by
        simpa [rawMap, rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ W hWopen hz₀W) with
    ⟨V, hVopen, hz₀V, hVW, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hreadback_bridge⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hz, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.A1passive z.F2 z.A3passive z.Ctop
        z.F3 z.yNext hz rfl
  refine ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleftV,
    hsource_inj, hsource_contOn, hsource_image, himage_p13V, ?_⟩
  dsimp only at hfinite ⊢
  refine ⟨hfinite.1, ?_⟩
  intro chartPiece hchartPiece_meas hchartPiece_sub_local hchartPiece_sub_image
    hraw_push density Kprior hdensity
  let D : ℝ≥0∞ := ((cHaar⁻¹ : NNReal) : ℝ≥0∞)
  have hpiece_U : chartPiece ⊆ U := fun E hE ↦
    (hchartPiece_sub_local hE).1
  have hpiece_sourceStratum : chartPiece ⊆ sourceStratum := fun E hE ↦
    (hchartPiece_sub_local hE).2
  have hpiece_p13 : chartPiece ⊆ p13SourceSet := fun E hE ↦
    himage_p13V E (hchartPiece_sub_image hE)
  have hright : ∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E := by
    intro E hE
    rcases hchartPiece_sub_image hE with ⟨z, hzV, rfl⟩
    constructor
    · rw [hleftV z hzV]
      exact hVW hzV
    · rw [hleftV z hzV]
  have hreadback_volume :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          D • coordinateSourceMeasure.restrict W := by
    simpa [rawMap, rawSourceSet, d, originalVolume, cHaar, D] using
      hreadback_bridge coordinateSourceMeasure m chartPiece hchartPiece_meas
        hchartPiece_sub_image hraw_push
  have hD : D < ∞ := by
    simp [D]
  simpa [originalVolume, D] using
    hfinite.2 hchartPiece_meas hpiece_U hpiece_sourceStratum
      (by simpa [p13SourceSet] using hpiece_p13)
      (by simpa [sourceChart, readback] using hright)
      (density := density) (Kprior := Kprior) hdensity
      (Csource := D)
      (by simpa [EdgeFamily, readback, originalVolume] using hreadback_volume.1)
      (by simpa [EdgeFamily, readback, originalVolume] using hreadback_volume.2)
      hD

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This packages the large Case 2 finite-integral socket with the reverse-domination readback bridge.
/-- Original edge-family priors feed into the Case 2 finite-integral socket
from a finite reverse raw-source domination hypothesis.

This is the domination analogue of the raw-pushforward equality wrapper above:
for chart pieces inside the actual source-chart image, a finite domination
`rawHaar.restrict rawSourceSet ≤ D • Measure.map rawMap
(coordinateSourceMeasure.restrict V)` supplies the original-volume readback
domination required by the direct finite-integral front end.

The reverse raw-source domination remains a chart-piece hypothesis.  This
theorem does not prove determinant-chart Haar transport, raw-order Haar
transport, original source-prior transport, source-image coverage, source-rank
coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (m :
      Measure
        (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ))
    [m.IsAddHaarMeasure]
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure] [SFinite ν]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
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
    let passiveSource := passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
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
    let baseJ := passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
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
    let rawDetChart :
        Set (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet :
        Set (TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let p13SourceChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let cHaar :=
      ((Measure.map
          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
            W₂ B₂ U₀)
          m).addHaarScalarFactor (originalTupleVolume d))
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    ∃ V : Set
                      (Case2PassiveTheta
                        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
                        (∀ z ∈ V, readback (sourceChart z) = z) ∧
                        Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                        MeasurableSet (sourceChart '' V) ∧
                        (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                    let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                    MeasurableSet sourceLocal ∧
                      ∀ {chartPiece : Set EdgeFamily},
                        MeasurableSet chartPiece →
                          chartPiece ⊆ sourceLocal →
                            chartPiece ⊆ sourceChart '' V →
                              ∀ {D : ℝ≥0∞},
                                m.restrict rawSourceSet ≤
                                  D • Measure.map rawMap
                                    (coordinateSourceMeasure.restrict V) →
                                  D < ∞ →
                                    ∀ {density : EdgeFamily → ℝ} {Kprior : ℝ},
                                      (∀ᵐ E ∂(originalEdgeFamilyVolume
                                        (V := reverseVertex W₂)
                                        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)).restrict
                                          chartPiece,
                                          density E ≤ Kprior) →
                                                  (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                                    ENNReal.ofReal
                                                      ((Metric.ball
                                                        (0 : EuclideanSpace ℝ ρreg) R).indicator
                                                        (fun u ↦
                                                          (loss (z.1, u)) ^
                                                            (-(t +
                                                              (aoyagiTheorem2RegularVariableCount
                                                                  2 H r : ℝ) /
                                                                2))) z.2) ∂
                                                    ((originalEdgeFamilyPrior (V := reverseVertex W₂)
                                                      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                                      density).restrict chartPiece).prod ν) <
                                                      ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y rawMap
    jacobianDensity baseJ EdgeFamily sourceChart readback sourceDensity
    coordinateSourceMeasure base ρreg sourceStratum rawDetChart rawSourceSet
    p13SourceSet p13SourceChart d originalVolume cHaar hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, base, ρreg, sourceStratum,
          rawDetChart, p13SourceChart, d, cHaar] using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top m Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  have hsourceChart' :
      AEMeasurable
        (case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W) := by
    simpa [sourceChart, baseJ, passiveSource] using hsourceChart
  have hsourceImageDensity' :
      AEMeasurable sourceImageDensity
        (Measure.map
          (case2PassiveThetaEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
          (((passiveMeasure.prod weightedBox).withDensity jacobianDensity).restrict W)) := by
    simpa [sourceImageBase, sourceChart, baseJ, passiveSource] using
      hsourceImageDensity
  rcases
      hsocket hsourceChart' hsourceImageDensity'
        (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, hfinite⟩
  rcases
      (by
        simpa [rawMap, rawSourceSet, p13SourceSet, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ W hWopen hz₀W) with
    ⟨V, hVopen, hz₀V, hVW, hleft, hsource_inj, hsource_contOn,
      hsource_image, himage_p13, hreadback_bridge⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hz, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13 (sourceChart z) z.A1passive z.F2 z.A3passive z.Ctop
        z.F3 z.yNext hz rfl
  refine ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hVW, hleftV,
    hsource_inj, hsource_contOn, hsource_image, himage_p13V, ?_⟩
  dsimp only at hfinite ⊢
  refine ⟨hfinite.1, ?_⟩
  intro chartPiece hchartPiece_meas hchartPiece_sub_local hchartPiece_sub_image
    D hraw_dom hD density Kprior hdensity
  let Dvol : ℝ≥0∞ := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * D)
  have hpiece_U : chartPiece ⊆ U := fun E hE ↦
    (hchartPiece_sub_local hE).1
  have hpiece_sourceStratum : chartPiece ⊆ sourceStratum := fun E hE ↦
    (hchartPiece_sub_local hE).2
  have hpiece_p13 : chartPiece ⊆ p13SourceSet := fun E hE ↦
    himage_p13V E (hchartPiece_sub_image hE)
  have hright : ∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E := by
    intro E hE
    rcases hchartPiece_sub_image hE with ⟨z, hzV, rfl⟩
    constructor
    · rw [hleftV z hzV]
      exact hVW hzV
    · rw [hleftV z hzV]
  have hreadback_volume :
      AEMeasurable readback (originalVolume.restrict chartPiece) ∧
        Measure.map readback (originalVolume.restrict chartPiece) ≤
          Dvol • coordinateSourceMeasure.restrict W := by
    simpa [rawMap, rawSourceSet, d, originalVolume, cHaar, Dvol] using
      hreadback_bridge coordinateSourceMeasure m chartPiece (D := D)
        hchartPiece_meas hchartPiece_sub_image hraw_dom
  have hDvol : Dvol < ∞ := by
    dsimp [Dvol]
    exact ENNReal.mul_lt_top (by simp) hD
  simpa [originalVolume, Dvol] using
    hfinite.2 hchartPiece_meas hpiece_U hpiece_sourceStratum
      (by simpa [p13SourceSet] using hpiece_p13)
      (by simpa [sourceChart, readback] using hright)
      (density := density) (Kprior := Kprior) hdensity
      (Csource := Dvol)
      (by simpa [EdgeFamily, readback, originalVolume] using hreadback_volume.1)
      (by simpa [EdgeFamily, readback, originalVolume] using hreadback_volume.2)
      hDvol

end PaperEndpointFixedBaseRegularCoordinateSourceData
end Aoyagi
end DLN
end DLNFibre
