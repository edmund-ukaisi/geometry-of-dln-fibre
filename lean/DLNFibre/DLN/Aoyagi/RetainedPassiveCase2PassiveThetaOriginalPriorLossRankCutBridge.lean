import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge
import DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure

/-!
# Case 2 with-following original-prior rank-cut local original-loss bridge

This file feeds the rank-cut original-prior residual-source hypotheses into
the local-source finite-integral socket for the original square-Frobenius
`lossDLN`.  The residual zero-locus nullity, adapted-product lower bound,
regular-coordinate density bounds, and source-data alignment remain explicit.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

universe v

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The statement threads the large rank-cut source package into the local loss socket.
/-- Conditional local original-loss finite-integral handoff on the with-following
rank-cut p.13/readback patch for the original edge-family prior.

The theorem first constructs the same rank-cut patch as the residual-source
bridge.  After an explicit residual zero-locus-nullity hypothesis on that
restricted original prior, the returned continuation applies the local-source
`lossDLN` socket under explicit adapted-product and density bounds.  It does
not prove zero-locus nullity, density comparison, source/prior transport,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_localSource_bounds
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
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
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
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 < t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {priorDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    (hprior_cont :
      ContinuousAt priorDensity
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀))
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G)
    (hGdet :
      G ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    let μprior : Measure EdgeFamily :=
      originalEdgeFamilyPrior
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        priorDensity
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
              IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                  MeasurableSet ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                    (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                      sourceChart '' (V ∩ rankEq) =
                        (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                        ∀ (rawHaar : Measure RawTuple), rawHaar.IsAddHaarMeasure →
                          (μprior.restrict
                            ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum))
                            {E | aoyagiCoordinateSquareSum
                              (paperEndpointFixedBaseResidualBlockCoordinateMap
                                (K := ℝ) W₂ B₂ U₀ hU₀
                                (fun E : EdgeFamily ↦ E) E) = 0} = 0 →
                          ∀ {H : ℕ → ℕ},
                            PaperEndpointFixedBaseRegularCoordinateSourceData
                              (K := ℝ) W₂ B₂ U₀ hU₀ (sourceChart z₀)
                              (fun E : EdgeFamily ↦ E) H r rEdge →
                          ∀ {d : Fin 3 → ℕ},
                            (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j)) →
                          ∀ {ν : Measure (EuclideanSpace ℝ ρreg)}, ν.IsAddHaarMeasure →
                          ∀ {lossDensity : EdgeFamily × EuclideanSpace ℝ ρreg → ℝ}
                            {R c C : ℝ},
                            0 < R → 0 < c → 0 ≤ C →
                            (∀ᶠ E in nhdsWithin (sourceChart z₀)
                                ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
                              ∀ u : EuclideanSpace ℝ ρreg,
                                u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
                                  c * (aoyagiCoordinateSquareSum
                                      (paperEndpointFixedBaseResidualBlockCoordinateMap
                                        (K := ℝ) W₂ B₂ U₀ hU₀
                                        (fun E : EdgeFamily ↦ E) E) +
                                    aoyagiCoordinateSquareSum (fun i => u i)) ≤
                                  paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                                    (K := ℝ) W₂ B₂ U₀ hU₀ CedgeProd (E, u)) →
                            (∀ᶠ E in nhdsWithin (sourceChart z₀)
                                ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
                              ∀ u : EuclideanSpace ℝ ρreg,
                                u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
                                  0 ≤ lossDensity (E, u)) →
                            (∀ᶠ E in nhdsWithin (sourceChart z₀)
                                ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
                              ∀ u : EuclideanSpace ℝ ρreg,
                                u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
                                  lossDensity (E, u) ≤ C) →
                            ∃ U : Set EdgeFamily, IsOpen U ∧ sourceChart z₀ ∈ U ∧
                              (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                ENNReal.ofReal
                                  ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                                    (fun u =>
                                      (lossDLN d
                                        (LinearMap.toMatrix (b 0) (b (Fin.last 2))
                                          (chainMap (reverseVertex W₂) (reverseEdge W₂ B₂)
                                            0 (Fin.last 2) (Fin.zero_le (Fin.last 2))))
                                        (chainMapMatrixTuple b
                                          (fun p : Fin 2 =>
                                            (CedgeProd (z.1, u) p :
                                              reverseVertex W₂ p.castSucc →ₗ[ℝ]
                                                reverseVertex W₂ p.succ)))) ^
                                        (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                                        lossDensity (z.1, u)) z.2) ∂
                                  (μprior.restrict
                                    (U ∩ ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum))).prod ν) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet sourceStratum rankEq
    μprior ρreg CedgeProd
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, sourceChart, readback, p13SourceSet,
          sourceStratum, rankEq, μprior] using
          exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_continuousAt_priorDensity_of_subset_detSector
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) (le_of_lt ht) hcrit (density := priorDensity) hprior_cont
            G hGopen hz₀G hGdet (r := r) (rEdge := rEdge) hprod) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV,
      himage_rank, hresidual_source⟩
  have hleft' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
  have hiffV' : ∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq := by
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
    simpa [sourceChart, sourceStratum, rankEq,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hiffV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  refine
    ⟨V, hVopen, hz₀V, hVG, hleft', hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV',
      himage_rank, ?_⟩
  intro rawHaar hrawHaar hzero H sourceData d b ν hν lossDensity R c C hR hc hC
    hadapted_lower hdensity_nonneg hdensity_le
  letI : rawHaar.IsAddHaarMeasure := hrawHaar
  letI : ν.IsAddHaarMeasure := hν
  rcases hresidual_source rawHaar hzero with ⟨hpos_source, hbase_source⟩
  simpa [ρreg, CedgeProd, μprior] using
    exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_adaptedProductDifferenceSquareSum_lower
      (W := W₂) (B := B₂) sourceData b
      (source := (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum)
      (μ := μprior) (ν := ν) (CedgeProd := CedgeProd)
      (density := lossDensity) (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht hrankPiece_meas hpos_source hbase_source
      (by simpa [ρreg, CedgeProd] using hadapted_lower)
      (by simpa [ρreg] using hdensity_nonneg)
      (by simpa [ρreg] using hdensity_le)

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This statement produces the adapted lower-bound radius before calling the local loss socket.
/-- Conditional local original-loss finite-integral handoff with the p.13
adapted-product lower-bound input produced from the fixed-base self-base
product-coordinate theorem.

The source base point must be aligned with the fixed reverse-edge family; this
centering hypothesis is explicit.  The theorem still assumes residual
zero-locus nullity and keeps the regular-coordinate density bounds explicit. -/
theorem exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_density_bounds
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
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
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
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 < t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {priorDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    (hprior_cont :
      ContinuousAt priorDensity
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀))
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G)
    (hGdet :
      G ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    let μprior : Measure EdgeFamily :=
      originalEdgeFamilyPrior
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        priorDensity
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
              IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                  MeasurableSet ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                    (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                      sourceChart '' (V ∩ rankEq) =
                        (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                        ∀ (rawHaar : Measure RawTuple), rawHaar.IsAddHaarMeasure →
                          (μprior.restrict
                            ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum))
                            {E | aoyagiCoordinateSquareSum
                              (paperEndpointFixedBaseResidualBlockCoordinateMap
                                (K := ℝ) W₂ B₂ U₀ hU₀
                                (fun E : EdgeFamily ↦ E) E) = 0} = 0 →
                          ∀ {H : ℕ → ℕ},
                            PaperEndpointFixedBaseRegularCoordinateSourceData
                              (K := ℝ) W₂ B₂ U₀ hU₀ (sourceChart z₀)
                              (fun E : EdgeFamily ↦ E) H r rEdge →
                            sourceChart z₀ =
                              (fun p : Fin 2 ↦
                                LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) →
                          ∀ {d : Fin 3 → ℕ},
                            (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j)) →
                          ∀ {ν : Measure (EuclideanSpace ℝ ρreg)}, ν.IsAddHaarMeasure →
                          ∀ {Rmax : ℝ}, 0 < Rmax →
                            ∃ R c : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 < c ∧
                              ∀ {lossDensity :
                                  EdgeFamily × EuclideanSpace ℝ ρreg → ℝ}
                                {C : ℝ},
                                0 ≤ C →
                                (∀ᶠ E in nhdsWithin (sourceChart z₀)
                                    ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
                                  ∀ u : EuclideanSpace ℝ ρreg,
                                    u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) Rmax →
                                      0 ≤ lossDensity (E, u)) →
                                (∀ᶠ E in nhdsWithin (sourceChart z₀)
                                    ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
                                  ∀ u : EuclideanSpace ℝ ρreg,
                                    u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) Rmax →
                                      lossDensity (E, u) ≤ C) →
                                ∃ U : Set EdgeFamily, IsOpen U ∧ sourceChart z₀ ∈ U ∧
                                  (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                    ENNReal.ofReal
                                      ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                                        (fun u =>
                                          (lossDLN d
                                            (LinearMap.toMatrix (b 0) (b (Fin.last 2))
                                              (chainMap
                                                (reverseVertex W₂) (reverseEdge W₂ B₂)
                                                0 (Fin.last 2) (Fin.zero_le (Fin.last 2))))
                                            (chainMapMatrixTuple b
                                              (fun p : Fin 2 =>
                                                (CedgeProd (z.1, u) p :
                                                  reverseVertex W₂ p.castSucc →ₗ[ℝ]
                                                    reverseVertex W₂ p.succ)))) ^
                                            (-(t +
                                              (aoyagiTheorem2RegularVariableCount 2 H r :
                                                ℝ) / 2)) *
                                            lossDensity (z.1, u)) z.2) ∂
                                      (μprior.restrict
                                        (U ∩
                                          ((p13SourceSet ∩ readback ⁻¹' V) ∩
                                            sourceStratum))).prod ν) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet sourceStratum rankEq
    μprior ρreg CedgeProd
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, p13SourceSet,
          sourceStratum, rankEq, μprior, CedgeProd] using
          exists_open_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_localSource_bounds
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (priorDensity := priorDensity) hprior_cont
            G hGopen hz₀G hGdet (r := r) (rEdge := rEdge) hprod) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV,
      himage_rank, hlocal_loss⟩
  have hleft' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
  have hiffV' : ∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq := by
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
    simpa [sourceChart, sourceStratum, rankEq,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hiffV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  refine
    ⟨V, hVopen, hz₀V, hVG, hleft', hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV',
      himage_rank, ?_⟩
  intro rawHaar hrawHaar hzero H sourceData hsource_base d b ν hν Rmax hRmax
  have hCedgeBase :
      ContinuousAt (fun E : EdgeFamily ↦ E) (sourceChart z₀) := by
    simpa using
      (continuous_id.continuousAt :
        ContinuousAt (fun E : EdgeFamily ↦ E) (sourceChart z₀))
  rcases
      exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
        (V := W₂) (Bv := B₂) (x₀ := sourceChart z₀) U₀ hU₀
        (fun E : EdgeFamily ↦ E) hCedgeBase hsource_base
        (r := r) (rEdge := rEdge) (Rmax := Rmax) hRmax with
    ⟨R, c, hR, hR_le_Rmax, hc, hadapted_stratum⟩
  refine ⟨R, c, hR, hR_le_Rmax, hc, ?_⟩
  intro lossDensity C hC hdensity_nonneg hdensity_le
  have hsource_subset :
      ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ⊆ sourceStratum :=
    Set.inter_subset_right
  have hadapted_full :
      ∀ᶠ E in nhdsWithin (sourceChart z₀) sourceStratum,
        ∀ u : EuclideanSpace ℝ ρreg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀
                  (fun E : EdgeFamily ↦ E) E) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W₂ B₂ U₀ hU₀ CedgeProd (E, u) := by
    simpa [ρreg, CedgeProd, sourceStratum] using hadapted_stratum
  have hadapted_rank :
      ∀ᶠ E in nhdsWithin (sourceChart z₀)
          ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
        ∀ u : EuclideanSpace ℝ ρreg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀
                  (fun E : EdgeFamily ↦ E) E) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W₂ B₂ U₀ hU₀ CedgeProd (E, u) :=
    hadapted_full.filter_mono (nhdsWithin_mono _ hsource_subset)
  have hdensity_nonneg_R :
      ∀ᶠ E in nhdsWithin (sourceChart z₀)
          ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
        ∀ u : EuclideanSpace ℝ ρreg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
            0 ≤ lossDensity (E, u) :=
    hdensity_nonneg.mono fun E hE u hu =>
      hE u (Metric.ball_subset_ball hR_le_Rmax hu)
  have hdensity_le_R :
      ∀ᶠ E in nhdsWithin (sourceChart z₀)
          ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
        ∀ u : EuclideanSpace ℝ ρreg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
            lossDensity (E, u) ≤ C :=
    hdensity_le.mono fun E hE u hu =>
      hE u (Metric.ball_subset_ball hR_le_Rmax hu)
  simpa [ρreg, CedgeProd, μprior] using
    hlocal_loss rawHaar hrawHaar hzero sourceData b (ν := ν) hν
      (lossDensity := lossDensity) (R := R) (c := c) (C := C)
      hR hc hC hadapted_rank hdensity_nonneg_R hdensity_le_R

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This statement obtains the regular-coordinate density bounds from continuity.
/-- Conditional local original-loss finite-integral handoff with both the
p.13 adapted-product lower-bound input and the regular-coordinate density
bounds produced by local continuity/positivity.

The supplied scalar density is an edge-family density pulled back along the
fixed-base p.13 product-coordinate map.  This is only a topological density
bound; the theorem does not identify or transport the original statistical
prior through the product-coordinate map. -/
theorem exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_continuousAt_pos_density
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
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
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
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 < t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {priorDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    (hprior_cont :
      ContinuousAt priorDensity
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀))
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G)
    (hGdet :
      G ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    let μprior : Measure EdgeFamily :=
      originalEdgeFamilyPrior
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        priorDensity
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
              IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                  MeasurableSet ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                    (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                      sourceChart '' (V ∩ rankEq) =
                        (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                        ∀ (rawHaar : Measure RawTuple), rawHaar.IsAddHaarMeasure →
                          (μprior.restrict
                            ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum))
                            {E | aoyagiCoordinateSquareSum
                              (paperEndpointFixedBaseResidualBlockCoordinateMap
                                (K := ℝ) W₂ B₂ U₀ hU₀
                                (fun E : EdgeFamily ↦ E) E) = 0} = 0 →
                          ∀ {H : ℕ → ℕ},
                            PaperEndpointFixedBaseRegularCoordinateSourceData
                              (K := ℝ) W₂ B₂ U₀ hU₀ (sourceChart z₀)
                              (fun E : EdgeFamily ↦ E) H r rEdge →
                            sourceChart z₀ =
                              (fun p : Fin 2 ↦
                                LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) →
                          ∀ {d : Fin 3 → ℕ},
                            (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j)) →
                          ∀ {ν : Measure (EuclideanSpace ℝ ρreg)}, ν.IsAddHaarMeasure →
                          ∀ {edgeDensity : EdgeFamily → ℝ} {Rmax : ℝ},
                            ContinuousAt edgeDensity
                              (CedgeProd
                                (sourceChart z₀, (0 : EuclideanSpace ℝ ρreg))) →
                            0 <
                              edgeDensity
                                (CedgeProd
                                  (sourceChart z₀, (0 : EuclideanSpace ℝ ρreg))) →
                            0 < Rmax →
                            ∃ R c C : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 < c ∧ 0 ≤ C ∧
                              ∃ U : Set EdgeFamily, IsOpen U ∧ sourceChart z₀ ∈ U ∧
                                (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                  ENNReal.ofReal
                                    ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                                      (fun u =>
                                        (lossDLN d
                                          (LinearMap.toMatrix (b 0) (b (Fin.last 2))
                                            (chainMap
                                              (reverseVertex W₂) (reverseEdge W₂ B₂)
                                              0 (Fin.last 2) (Fin.zero_le (Fin.last 2))))
                                          (chainMapMatrixTuple b
                                            (fun p : Fin 2 =>
                                              (CedgeProd (z.1, u) p :
                                                reverseVertex W₂ p.castSucc →ₗ[ℝ]
                                                  reverseVertex W₂ p.succ)))) ^
                                          (-(t +
                                            (aoyagiTheorem2RegularVariableCount 2 H r :
                                              ℝ) / 2)) *
                                          edgeDensity (CedgeProd (z.1, u))) z.2) ∂
                                    (μprior.restrict
                                      (U ∩
                                        ((p13SourceSet ∩ readback ⁻¹' V) ∩
                                          sourceStratum))).prod ν) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet sourceStratum rankEq
    μprior ρreg CedgeProd
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, p13SourceSet,
          sourceStratum, rankEq, μprior, CedgeProd] using
          exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_density_bounds
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (priorDensity := priorDensity) hprior_cont
            G hGopen hz₀G hGdet (r := r) (rEdge := rEdge) hprod) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV,
      himage_rank, hlocal_loss⟩
  have hleft' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
  have hiffV' : ∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq := by
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
    simpa [sourceChart, sourceStratum, rankEq,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hiffV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  refine
    ⟨V, hVopen, hz₀V, hVG, hleft', hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV',
      himage_rank, ?_⟩
  intro rawHaar hrawHaar hzero H sourceData hsource_base d b ν hν edgeDensity Rmax
    hedge_cont hedge_pos hRmax
  have hCedgeBase :
      ContinuousAt (fun E : EdgeFamily ↦ E) (sourceChart z₀) := by
    simpa using
      (continuous_id.continuousAt :
        ContinuousAt (fun E : EdgeFamily ↦ E) (sourceChart z₀))
  rcases
      exists_pos_radius_le_eventually_nhdsWithin_density_comp_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_bounds_of_continuousAt_pos
        (V := W₂) (Bv := B₂) (α := EdgeFamily) (x₀ := sourceChart z₀)
        U₀ hU₀ (fun E : EdgeFamily ↦ E) hCedgeBase hsource_base
        (source := ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum))
        (density := edgeDensity) (Rmax := Rmax)
        (by simpa [ρreg, CedgeProd] using hedge_cont)
        (by simpa [ρreg, CedgeProd] using hedge_pos)
        hRmax with
    ⟨Rden, C, hRden, hRden_le_Rmax, hC, hdensity_nonneg, hdensity_le⟩
  rcases
      hlocal_loss rawHaar hrawHaar hzero sourceData hsource_base b
        (ν := ν) hν (Rmax := Rden) hRden with
    ⟨R, hR, hR_le_Rden, hc_exists, hloss⟩
  rcases hc_exists with ⟨c, hc⟩
  rcases
      hloss (lossDensity := fun z : EdgeFamily × EuclideanSpace ℝ ρreg ↦
          edgeDensity (CedgeProd z)) (C := C) hC
        (by simpa [ρreg, CedgeProd] using hdensity_nonneg)
        (by simpa [ρreg, CedgeProd] using hdensity_le) with
    ⟨U, hUopen, hbaseU, hfin⟩
  exact
    ⟨R, c, C, hR, le_trans hR_le_Rden hRden_le_Rmax, hc, hC,
      U, hUopen, hbaseU, by simpa [ρreg, CedgeProd, μprior] using hfin⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper repeats the large rank-cut endpoint statement before specializing the final density.
/-- Prior-density specialization of the continuous pulled-back density
rank-cut local original-loss handoff.

The density in the integrand is the same scalar function that defines the
original edge-family prior, evaluated after the p.13 product-coordinate map.
Continuity and positivity are assumed at the actual product-zero representative
`CedgeProd (sourceChart z0, 0)`.  They are not derived from continuity at
`sourceChart z0`, because the product-zero representative is not generally the
source-chart base edge family. -/
theorem exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_continuousAt_pos_priorDensity_product_zero
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
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
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
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 < t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {priorDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    (hprior_cont :
      ContinuousAt priorDensity
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀))
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G)
    (hGdet :
      G ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    let μprior : Measure EdgeFamily :=
      originalEdgeFamilyPrior
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        priorDensity
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
              IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                  MeasurableSet ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                    (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                      sourceChart '' (V ∩ rankEq) =
                        (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                        ∀ (rawHaar : Measure RawTuple), rawHaar.IsAddHaarMeasure →
                          (μprior.restrict
                            ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum))
                            {E | aoyagiCoordinateSquareSum
                              (paperEndpointFixedBaseResidualBlockCoordinateMap
                                (K := ℝ) W₂ B₂ U₀ hU₀
                                (fun E : EdgeFamily ↦ E) E) = 0} = 0 →
                          ∀ {H : ℕ → ℕ},
                            PaperEndpointFixedBaseRegularCoordinateSourceData
                              (K := ℝ) W₂ B₂ U₀ hU₀ (sourceChart z₀)
                              (fun E : EdgeFamily ↦ E) H r rEdge →
                            sourceChart z₀ =
                              (fun p : Fin 2 ↦
                                LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) →
                          ∀ {d : Fin 3 → ℕ},
                            (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j)) →
                          ∀ {ν : Measure (EuclideanSpace ℝ ρreg)}, ν.IsAddHaarMeasure →
                          ∀ {Rmax : ℝ},
                            ContinuousAt priorDensity
                              (CedgeProd
                                (sourceChart z₀, (0 : EuclideanSpace ℝ ρreg))) →
                            0 <
                              priorDensity
                                (CedgeProd
                                  (sourceChart z₀, (0 : EuclideanSpace ℝ ρreg))) →
                            0 < Rmax →
                            ∃ R c C : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 < c ∧ 0 ≤ C ∧
                              ∃ U : Set EdgeFamily, IsOpen U ∧ sourceChart z₀ ∈ U ∧
                                (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                  ENNReal.ofReal
                                    ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                                      (fun u =>
                                        (lossDLN d
                                          (LinearMap.toMatrix (b 0) (b (Fin.last 2))
                                            (chainMap
                                              (reverseVertex W₂) (reverseEdge W₂ B₂)
                                              0 (Fin.last 2) (Fin.zero_le (Fin.last 2))))
                                          (chainMapMatrixTuple b
                                            (fun p : Fin 2 =>
                                              (CedgeProd (z.1, u) p :
                                                reverseVertex W₂ p.castSucc →ₗ[ℝ]
                                                  reverseVertex W₂ p.succ)))) ^
                                          (-(t +
                                            (aoyagiTheorem2RegularVariableCount 2 H r :
                                              ℝ) / 2)) *
                                          priorDensity (CedgeProd (z.1, u))) z.2) ∂
                                    (μprior.restrict
                                      (U ∩
                                        ((p13SourceSet ∩ readback ⁻¹' V) ∩
                                          sourceStratum))).prod ν) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet sourceStratum rankEq
    μprior ρreg CedgeProd
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, p13SourceSet,
          sourceStratum, rankEq, μprior, CedgeProd] using
          exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_continuousAt_pos_density
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (priorDensity := priorDensity) hprior_cont
            G hGopen hz₀G hGdet (r := r) (rEdge := rEdge) hprod) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV,
      himage_rank, hlocal_loss⟩
  have hleft' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
  have hiffV' : ∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq := by
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
    simpa [sourceChart, sourceStratum, rankEq,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hiffV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  refine
    ⟨V, hVopen, hz₀V, hVG, hleft', hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV',
      himage_rank, ?_⟩
  intro rawHaar hrawHaar hzero H sourceData hsource_base d b ν hν Rmax
    hprior_prod_cont hprior_prod_pos hRmax
  simpa [ρreg, CedgeProd, μprior] using
      hlocal_loss rawHaar hrawHaar hzero sourceData hsource_base b
        (ν := ν) hν (edgeDensity := priorDensity) (Rmax := Rmax)
        hprior_prod_cont hprior_prod_pos hRmax

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper repeats the large endpoint statement to specialize the endpoint bases.
/-- `Module.finBasis` endpoint-basis specialization of the prior-density product-zero
rank-cut local original-loss handoff.

The only change from the previous theorem is that the endpoint dimensions and
bases in `lossDLN` are fixed to `Module.finrank` and `Module.finBasis` for the
three reverse vertices.  All measure, source-data, centering, and product-zero
density hypotheses remain explicit. -/
theorem exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_continuousAt_pos_priorDensity_product_zero_finBasis
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
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
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
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 < t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {priorDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    (hprior_cont :
      ContinuousAt priorDensity
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀))
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G)
    (hGdet :
      G ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    let μprior : Measure EdgeFamily :=
      originalEdgeFamilyPrior
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        priorDensity
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    let d : Fin 3 → ℕ := fun j ↦ Module.finrank ℝ (reverseVertex W₂ j)
    let b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j) :=
      fun j ↦ Module.finBasis ℝ (reverseVertex W₂ j)
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
              IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                  MeasurableSet ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                    (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                      sourceChart '' (V ∩ rankEq) =
                        (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                        ∀ (rawHaar : Measure RawTuple), rawHaar.IsAddHaarMeasure →
                          (μprior.restrict
                            ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum))
                            {E | aoyagiCoordinateSquareSum
                              (paperEndpointFixedBaseResidualBlockCoordinateMap
                                (K := ℝ) W₂ B₂ U₀ hU₀
                                (fun E : EdgeFamily ↦ E) E) = 0} = 0 →
                          ∀ {H : ℕ → ℕ},
                            PaperEndpointFixedBaseRegularCoordinateSourceData
                              (K := ℝ) W₂ B₂ U₀ hU₀ (sourceChart z₀)
                              (fun E : EdgeFamily ↦ E) H r rEdge →
                            sourceChart z₀ =
                              (fun p : Fin 2 ↦
                                LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) →
                          ∀ {ν : Measure (EuclideanSpace ℝ ρreg)}, ν.IsAddHaarMeasure →
                          ∀ {Rmax : ℝ},
                            ContinuousAt priorDensity
                              (CedgeProd
                                (sourceChart z₀, (0 : EuclideanSpace ℝ ρreg))) →
                            0 <
                              priorDensity
                                (CedgeProd
                                  (sourceChart z₀, (0 : EuclideanSpace ℝ ρreg))) →
                            0 < Rmax →
                            ∃ R c C : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 < c ∧ 0 ≤ C ∧
                              ∃ U : Set EdgeFamily, IsOpen U ∧ sourceChart z₀ ∈ U ∧
                                (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                  ENNReal.ofReal
                                    ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                                      (fun u =>
                                        (lossDLN d
                                          (LinearMap.toMatrix (b 0) (b (Fin.last 2))
                                            (chainMap
                                              (reverseVertex W₂) (reverseEdge W₂ B₂)
                                              0 (Fin.last 2) (Fin.zero_le (Fin.last 2))))
                                          (chainMapMatrixTuple b
                                            (fun p : Fin 2 =>
                                              (CedgeProd (z.1, u) p :
                                                reverseVertex W₂ p.castSucc →ₗ[ℝ]
                                                  reverseVertex W₂ p.succ)))) ^
                                          (-(t +
                                            (aoyagiTheorem2RegularVariableCount 2 H r :
                                              ℝ) / 2)) *
                                          priorDensity (CedgeProd (z.1, u))) z.2) ∂
                                    (μprior.restrict
                                      (U ∩
                                        ((p13SourceSet ∩ readback ⁻¹' V) ∩
                                          sourceStratum))).prod ν) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet sourceStratum rankEq
    μprior ρreg CedgeProd d b
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, p13SourceSet,
          sourceStratum, rankEq, μprior, CedgeProd] using
          exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_continuousAt_pos_priorDensity_product_zero
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (priorDensity := priorDensity) hprior_cont
            G hGopen hz₀G hGdet (r := r) (rEdge := rEdge) hprod) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV,
      himage_rank, hlocal_loss⟩
  have hleft' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
  have hiffV' : ∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq := by
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
    simpa [sourceChart, sourceStratum, rankEq,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hiffV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  refine
    ⟨V, hVopen, hz₀V, hVG, hleft', hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV',
      himage_rank, ?_⟩
  intro rawHaar hrawHaar hzero H sourceData hsource_base ν hν Rmax
    hprior_prod_cont hprior_prod_pos hRmax
  simpa [ρreg, CedgeProd, μprior, d, b] using
      hlocal_loss rawHaar hrawHaar hzero sourceData hsource_base
        (fun j : Fin 3 ↦ Module.finBasis ℝ (reverseVertex W₂ j))
        (ν := ν) hν (Rmax := Rmax)
        hprior_prod_cont hprior_prod_pos hRmax

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This wrapper specializes the regular-coordinate Haar measure to coordinate volume.
/-- `Module.finBasis` and regular-coordinate `volume` specialization of the
prior-density product-zero rank-cut local original-loss handoff.

The raw Haar measure remains explicit.  Only the regular-coordinate additive
Haar measure is fixed to standard `EuclideanSpace` volume. -/
theorem exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_continuousAt_pos_priorDensity_product_zero_finBasis_volume
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
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
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
    [LocallyCompactSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [SecondCountableTopology
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
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (hF₀det : IsUnit ((z₀.2.submatrix id eNext.symm).det))
    {t : ℝ}
    (ht : 0 < t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {priorDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    (hprior_cont :
      ContinuousAt priorDensity
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀))
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G)
    (hGdet :
      G ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (hprod : Module.finrank ℝ (LinearMap.range (paperTotalMap W₂ B₂)) = r) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    let μprior : Measure EdgeFamily :=
      originalEdgeFamilyPrior
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        priorDensity
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
    let d : Fin 3 → ℕ := fun j ↦ Module.finrank ℝ (reverseVertex W₂ j)
    let b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j) :=
      fun j ↦ Module.finBasis ℝ (reverseVertex W₂ j)
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
              IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                  MeasurableSet ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                    (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                      sourceChart '' (V ∩ rankEq) =
                        (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                        ∀ (rawHaar : Measure RawTuple), rawHaar.IsAddHaarMeasure →
                          (μprior.restrict
                            ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum))
                            {E | aoyagiCoordinateSquareSum
                              (paperEndpointFixedBaseResidualBlockCoordinateMap
                                (K := ℝ) W₂ B₂ U₀ hU₀
                                (fun E : EdgeFamily ↦ E) E) = 0} = 0 →
                          ∀ {H : ℕ → ℕ},
                            PaperEndpointFixedBaseRegularCoordinateSourceData
                              (K := ℝ) W₂ B₂ U₀ hU₀ (sourceChart z₀)
                              (fun E : EdgeFamily ↦ E) H r rEdge →
                            sourceChart z₀ =
                              (fun p : Fin 2 ↦
                                LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) →
                          ∀ {Rmax : ℝ},
                            ContinuousAt priorDensity
                              (CedgeProd
                                (sourceChart z₀, (0 : EuclideanSpace ℝ ρreg))) →
                            0 <
                              priorDensity
                                (CedgeProd
                                  (sourceChart z₀, (0 : EuclideanSpace ℝ ρreg))) →
                            0 < Rmax →
                            ∃ R c C : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 < c ∧ 0 ≤ C ∧
                              ∃ U : Set EdgeFamily, IsOpen U ∧ sourceChart z₀ ∈ U ∧
                                (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                                  ENNReal.ofReal
                                    ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                                      (fun u =>
                                        (lossDLN d
                                          (LinearMap.toMatrix (b 0) (b (Fin.last 2))
                                            (chainMap
                                              (reverseVertex W₂) (reverseEdge W₂ B₂)
                                              0 (Fin.last 2) (Fin.zero_le (Fin.last 2))))
                                          (chainMapMatrixTuple b
                                            (fun p : Fin 2 =>
                                              (CedgeProd (z.1, u) p :
                                                reverseVertex W₂ p.castSucc →ₗ[ℝ]
                                                  reverseVertex W₂ p.succ)))) ^
                                          (-(t +
                                            (aoyagiTheorem2RegularVariableCount 2 H r :
                                              ℝ) / 2)) *
                                          priorDensity (CedgeProd (z.1, u))) z.2) ∂
                                    (μprior.restrict
                                      (U ∩
                                        ((p13SourceSet ∩ readback ⁻¹' V) ∩
                                          sourceStratum))).prod
                                      (volume : Measure (EuclideanSpace ℝ ρreg))) < ∞ := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet sourceStratum rankEq
    μprior ρreg CedgeProd d b
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, p13SourceSet,
          sourceStratum, rankEq, μprior, CedgeProd, d, b] using
          exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_continuousAt_pos_priorDensity_product_zero_finBasis
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (priorDensity := priorDensity) hprior_cont
            G hGopen hz₀G hGdet (r := r) (rEdge := rEdge) hprod) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV,
      himage_rank, hlocal_loss⟩
  have hleft' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
  have hiffV' : ∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq := by
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
    simpa [sourceChart, sourceStratum, rankEq,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hiffV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  refine
    ⟨V, hVopen, hz₀V, hVG, hleft', hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV',
      himage_rank, ?_⟩
  intro rawHaar hrawHaar hzero H sourceData hsource_base Rmax
    hprior_prod_cont hprior_prod_pos hRmax
  have hν :
      (volume : Measure (EuclideanSpace ℝ ρreg)).IsAddHaarMeasure := by
    infer_instance
  simpa [ρreg, CedgeProd, μprior, d, b] using
      hlocal_loss rawHaar hrawHaar hzero sourceData hsource_base
        (ν := (volume : Measure (EuclideanSpace ℝ ρreg))) hν
        (Rmax := Rmax) hprior_prod_cont hprior_prod_pos hRmax

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
