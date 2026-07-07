import DLNFibre.DLN.Aoyagi.OriginalCoordinatePriorSourceImageBridge

/-!
# Pushed original coordinate priors at the p.13 finite-integral socket

This file consumes the original-coordinate source-image domination bridge in
the existing p.13 source-image finite-integral socket.  It proves only measure
bookkeeping: the pushed flattened-coordinate prior, restricted to a local
chart piece, satisfies the readback-domination hypothesis expected by the
finite-integral theorem.

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

universe v

set_option linter.style.longLine false in
/-- A source-image domination for an external measure on `sourceChart '' V`
gives the readback-domination hypothesis on any measurable chart piece
supported in `sourceChart '' (V ∩ W)`.

This is pure local-source bookkeeping.  It does not identify the external
measure, construct source coverage, or provide any Haar/Jacobian theorem. -/
theorem aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_of_le_smul_sourceImageReference_restrict_image
    {Θ E : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [BorelSpace Θ] [PolishSpace Θ]
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [T2Space E]
    (sourceChart : Θ → E) (readback : E → Θ)
    (thetaReference : Measure Θ) (V W : Set Θ) (chartPiece : Set E)
    (externalMeasure : Measure E) (C : ℝ≥0∞)
    (hV : MeasurableSet V)
    (hVW : MeasurableSet (V ∩ W))
    (himageV : MeasurableSet (sourceChart '' V))
    (hchartPiece : MeasurableSet chartPiece)
    (hchartPiece_sub : chartPiece ⊆ sourceChart '' (V ∩ W))
    (hsource_contOn : ContinuousOn sourceChart V)
    (hsource_inj : Set.InjOn sourceChart V)
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta)
    (hdom :
      externalMeasure ≤
        C • (Measure.map sourceChart (thetaReference.restrict V)).restrict
          (sourceChart '' V)) :
    AEMeasurable readback (externalMeasure.restrict chartPiece) ∧
      Measure.map readback (externalMeasure.restrict chartPiece) ≤
        C • thetaReference.restrict W := by
  let sourceRef : Measure E :=
    Measure.map sourceChart (thetaReference.restrict V)
  let sourceRefImage : Measure E :=
    sourceRef.restrict (sourceChart '' V)
  have hsource_aemeas : AEMeasurable sourceChart (thetaReference.restrict V) :=
    hsource_contOn.aemeasurable hV
  have hsourceRefImage_eq : sourceRefImage = sourceRef := by
    dsimp [sourceRefImage, sourceRef]
    exact
      Measure.restrict_eq_self_of_ae_mem
        ((ae_map_iff hsource_aemeas himageV).2
          (by
            filter_upwards [ae_restrict_mem hV] with theta htheta
            exact ⟨theta, htheta, rfl⟩))
  have hreadback_source :
      AEMeasurable readback sourceRef := by
    exact
      aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
        sourceChart readback thetaReference V hV hsource_contOn hsource_inj
        hleft
  have hsource_pull :
      Measure.map readback sourceRef = thetaReference.restrict V :=
    measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
      sourceChart readback thetaReference V hV hsource_aemeas
      hreadback_source hleft
  have hpiece_le_source :
      externalMeasure.restrict chartPiece ≤ C • sourceRef := by
    have hpiece_le :
        externalMeasure.restrict chartPiece ≤ externalMeasure := by
      exact Measure.le_iff.2 fun s _hs ↦ Measure.restrict_le_self s
    have hdom_sourceImage : externalMeasure ≤ C • sourceRefImage := by
      simpa [sourceRefImage, sourceRef] using hdom
    have hdom_source : externalMeasure ≤ C • sourceRef := by
      simpa [hsourceRefImage_eq] using hdom_sourceImage
    exact hpiece_le.trans hdom_source
  have hread_map_V :
      AEMeasurable readback (externalMeasure.restrict chartPiece) ∧
        Measure.map readback (externalMeasure.restrict chartPiece) ≤
          C • thetaReference.restrict V :=
    readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure
      (sourceRef := sourceRef) (μ := externalMeasure.restrict chartPiece)
      (thetaRef := thetaReference.restrict V) (C := C)
      hreadback_source hsource_pull hpiece_le_source
  have hpiece_sub_V : chartPiece ⊆ sourceChart '' V := by
    intro E hE
    rcases hchartPiece_sub hE with ⟨theta, htheta, rfl⟩
    exact ⟨theta, htheta.1, rfl⟩
  have hmap_inter :
      Measure.map readback (externalMeasure.restrict chartPiece) ≤
        C • thetaReference.restrict (V ∩ W) :=
    measure_map_restrict_source_subset_image_le_smul_restrict_of_le_smul_restrict_superset
      (source := chartPiece) (V := V ∩ W) (G := V)
      (sourceChart := sourceChart) (readback := readback)
      (μ := externalMeasure) (θμ := thetaReference) (c := C)
      hchartPiece hVW hchartPiece_sub
      (by
        intro theta htheta
        exact hleft theta htheta.1)
      (Set.inter_subset_left)
      hread_map_V.1 hread_map_V.2
  have hrestrict_le :
      thetaReference.restrict (V ∩ W) ≤ thetaReference.restrict W :=
    Measure.restrict_mono Set.inter_subset_right le_rfl
  have hsmul_restrict_le :
      C • thetaReference.restrict (V ∩ W) ≤ C • thetaReference.restrict W := by
    refine Measure.le_iff.2 ?_
    intro s hs
    rw [Measure.smul_apply, Measure.smul_apply]
    exact mul_le_mul_right (hrestrict_le s) C
  exact ⟨hread_map_V.1, hmap_inter.trans hsmul_restrict_le⟩

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This theorem composes two large dependent Case 2 packages and a local
-- measure-transfer helper; elaboration needs extra heartbeats for instance
-- synthesis and dependent-let normalization.
/-- Pushed original coordinate priors feed into the p.13 readback finite
integral socket from the conditional source-image domination bridge.

The finite-integral conclusion is for the edge-family image of the flattened
coordinate prior, restricted first to the source-chart image returned by the
coordinate-prior bridge and then to a caller-supplied chart piece.  The chart
piece is required to lie in `sourceChart '' (V ∩ W)`, where `V` is the
coordinate-prior source-image shrink and `W` is the finite-integral socket
shrink; this makes the readback land in the correct local theta domain.

All source-image density, determinant/Haar domination, local prior-density
upper bounds, and coordinate-density measurability hypotheses remain explicit.
This theorem does not prove source coverage, Haar transport, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_map_originalCoordinatePrior_restrict_sourceChart_preimage_chartPiece_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceImageDensity_comp_sourceChart_lower_priorDensity_comp_sourceChart_upper
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
          (J + 2, J + 2)).card : ℝ) + 1)
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
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
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
    let coordinateSourceMeasure :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      baseJ.withDensity sourceDensity
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
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
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
                      ∃ V :
                        Set
                          (Case2PassiveTheta
                            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
                        IsOpen V ∧ z₀ ∈ V ∧
                          (∀ z ∈ V, readback (sourceChart z) = z) ∧
                          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                          MeasurableSet (sourceChart '' V) ∧
                          (∀ E ∈ sourceChart '' V, E ∈ p13SourceSet) ∧
                            let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                            MeasurableSet sourceLocal ∧
                              ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                                ∀ {Cdet : ℝ≥0∞},
                                  rawHaar.restrict rawDetChart ≤
                                    Cdet • Measure.map Y (passiveSource.restrict V) →
                                    Cdet < ∞ →
                                      ε ≠ 0 →
                                        ε ≠ ∞ →
                                          AEMeasurable
                                            (fun A : Tuple (k := ℝ) d ↦
                                              ENNReal.ofReal
                                                (coordDensity (canonicalCoord d A)))
                                            ((originalTupleVolume d).restrict
                                              ((tupleToEdgeFamily
                                                (V := reverseVertex W₂) b) ⁻¹'
                                                  (sourceChart '' V))) →
                                            ∀ {chartPiece : Set EdgeFamily},
                                              MeasurableSet chartPiece →
                                                chartPiece ⊆ sourceLocal →
                                                  chartPiece ⊆ sourceChart '' (V ∩ W) →
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
                                                      ((Measure.map toEdge
                                                        ((originalCoordinatePrior d coordDensity).restrict
                                                          (toEdge ⁻¹'
                                                            (sourceChart '' V)))).restrict
                                                        chartPiece).prod ν) <
                                                        ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart readback sourceDensity coordinateSourceMeasure
    base ρreg sourceStratum RawTuple rawDetChart p13SourceSet d b toEdge
    edgeDensity hsource_eventually hprior_eventually hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource,
          RawTuple, EdgeFamily, Y, jacobianDensity, baseJ, sourceChart,
          readback, sourceDensity, coordinateSourceMeasure, rawDetChart,
          p13SourceSet, d, b, toEdge, edgeDensity] using
          exists_open_subset_map_originalCoordinatePrior_restrict_sourceChart_preimage_le_smul_sourceImageReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceImageDensity_comp_sourceChart_lower_priorDensity_comp_sourceChart_upper
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceImageDensity passiveMeasure Rres
            (ε := ε) coordDensity (Kprior := Kprior)
            hsource_eventually hprior_eventually) with
    ⟨V, hVopen, hz₀V, hleftV_raw, hsource_injV, hsource_contOnV,
      hsource_imageV, himage_p13V_raw, hcoordPrior_package⟩
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftV_raw z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hz
  have himage_p13V : ∀ E ∈ sourceChart '' V, E ∈ p13SourceSet := by
    intro E hE
    rcases hE with ⟨z, hzV, rfl⟩
    simpa [sourceChart, p13SourceSet, case2PassiveThetaEndpointSourceChart,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      himage_p13V_raw (sourceChart z) z.A1passive z.F2 z.A3passive
        z.Ctop z.F3 z.yNext hzV rfl
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, readback,
          sourceDensity, coordinateSourceMeasure, base, ρreg, sourceStratum]
          using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalSourceMeasure_restrict_chartPiece_map_readback_le_smul_coordinateSourceMeasure_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  rcases
      hsocket hsourceChart hsourceImageDensity
        (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, hfinite⟩
  refine ⟨U, hUopen, hbaseU, V, hVopen, hz₀V, hleftV,
    hsource_injV, hsource_contOnV, hsource_imageV, himage_p13V, ?_⟩
  dsimp only at hfinite ⊢
  refine ⟨hfinite.1, ?_⟩
  intro rawHaar _instRawHaar Cdet hdet_dom hCdet hε_ne_zero hε_ne_top
    hdensity chartPiece hchartPiece_meas hchartPiece_sub_local
    hchartPiece_sub_imageVW
  let cHaar :=
    ((Measure.map
        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
          W₂ B₂ U₀)
        rawHaar).addHaarScalarFactor (originalTupleVolume d))
  let Ddet : ℝ≥0∞ := Cdet * ε⁻¹
  let Dvol : ℝ≥0∞ := ((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet
  let Cprior : ℝ≥0∞ := ENNReal.ofReal Kprior * Dvol
  let coordPriorImage :
      Measure
        (∀ p : Fin 2,
          reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) :=
    Measure.map toEdge
      ((originalCoordinatePrior d coordDensity).restrict
        (toEdge ⁻¹' (sourceChart '' V)))
  have hcoordPrior_dom :
      Cprior < ∞ ∧
        coordPriorImage ≤
          Cprior •
            (Measure.map sourceChart
              (coordinateSourceMeasure.restrict V)).restrict
                (sourceChart '' V) := by
    simpa [cHaar, Ddet, Dvol, Cprior, coordPriorImage, d, b, toEdge,
      edgeDensity, rawDetChart] using
      hcoordPrior_package rawHaar hdet_dom hCdet hε_ne_zero hε_ne_top
        hdensity
  have hVWmeas : MeasurableSet (V ∩ W) :=
    hVopen.measurableSet.inter hWopen.measurableSet
  have hreadback_dom :
      AEMeasurable readback (coordPriorImage.restrict chartPiece) ∧
        Measure.map readback (coordPriorImage.restrict chartPiece) ≤
          Cprior • coordinateSourceMeasure.restrict W :=
    aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_of_le_smul_sourceImageReference_restrict_image
      sourceChart readback coordinateSourceMeasure V W chartPiece
      coordPriorImage Cprior hVopen.measurableSet hVWmeas hsource_imageV
      hchartPiece_meas hchartPiece_sub_imageVW hsource_contOnV
      hsource_injV hleftV hcoordPrior_dom.2
  have hright :
      ∀ E ∈ chartPiece, readback E ∈ W ∧ sourceChart (readback E) = E := by
    intro E hE
    rcases hchartPiece_sub_imageVW hE with ⟨theta, htheta, rfl⟩
    have hleft_theta : readback (sourceChart theta) = theta :=
      hleftV theta htheta.1
    constructor
    · simpa [hleft_theta] using htheta.2
    · rw [hleft_theta]
  have hpiece_U : chartPiece ⊆ U := fun E hE ↦
    (hchartPiece_sub_local hE).1
  have hpiece_sourceStratum : chartPiece ⊆ sourceStratum := fun E hE ↦
    (hchartPiece_sub_local hE).2
  simpa [coordPriorImage, Cprior] using
    hfinite.2 hchartPiece_meas hpiece_U hpiece_sourceStratum hright
      (externalSourceMeasure := coordPriorImage) (Cpull := Cprior)
      hreadback_dom.1 hreadback_dom.2 hcoordPrior_dom.1

end PaperEndpointFixedBaseRegularCoordinateSourceData
end Aoyagi
end DLN
end DLNFibre

end
