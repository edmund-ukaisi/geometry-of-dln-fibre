import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaProductResidualBridge

/-!
# Case 2 with-following original-prior residual bridge

This file composes the with-following prior-density finite-integral theorem
with the fixed-base residual-power adapter.  It stops at
`residualNegPowerIntegrableOn`; it does not compare to the original `lossDLN`,
prove residual positivity, source-rank coverage, normal crossings, pole order,
or RLCT extraction.
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
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The proof composes a large prior-density theorem and expands product-coordinate records.
/-- With-following fixed-base residual negative-power integrability on the
open p.13/readback-preimage patch returned by the prior-density theorem.

The caller supplies an open theta-side set `G` contained in the determinant
sector, so the pointwise fixed-base residual/product-residual square-sum bridge
is available on the returned shrink `V ⊆ G`.  This still does not prove
residual positivity, original `lossDLN` comparison, source-rank coverage,
prior transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_residualNegPowerIntegrableOn_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_isOpen_case2PassiveThetaWithFollowingFactor_of_continuousAt_priorDensity_of_subset_detSector
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
    (ht : 0 ≤ t)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    {density :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    (hprior_cont :
      ContinuousAt density
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
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :
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
    ∃ V : Set Θ,
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, readback (sourceChart z) = z) ∧
          Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
            MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
              IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                  ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                    residualNegPowerIntegrableOn
                      (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                      (fun E : EdgeFamily ↦ E)
                      (p13SourceSet ∩ readback ⁻¹' V)
                      (originalEdgeFamilyPrior
                        (V := reverseVertex W₂)
                        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                        density)
                      t := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet
  have hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
    hGdet hz₀G
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, sourceChart, readback, p13SourceSet] using
          exists_open_lintegral_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_isOpen_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_of_continuousAt_priorDensity
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hdet₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont G hGopen hz₀G) with
    ⟨V, hVopen, hz₀V, hVG, hleft_raw, hsource_inj, hsource_contOn,
      hpiece_meas, hpatch_open, himage_eq, hfinite_readback⟩
  have hleft : ∀ z ∈ V, readback (sourceChart z) = z := by
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
      hleft_raw z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  refine
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hpiece_meas, hpatch_open, himage_eq, ?_⟩
  intro rawHaar hrawHaar
  refine
    residualNegPowerIntegrableOn_of_lintegral_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidual_eq
      W₂ B₂ n hS hcont hnext hU₀ eNext e hpiece_meas
      (hfinite_readback rawHaar) ?_
  intro E hE
  have hEimage : E ∈ sourceChart '' V := by
    rw [himage_eq]
    exact hE
  rcases hEimage with ⟨z, hzV, rfl⟩
  have hdet_z :
      (case2PassiveThetaWithFollowingFactorEndpointRetainedData
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e).detChart := by
    exact
      case2PassiveThetaWithFollowingFactorEndpointRetainedData_detChart
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
        (hGdet (hVG hzV))
  have hsq_source :
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀
            (fun E : EdgeFamily ↦ E) (sourceChart z)) =
        aoyagiCoordinateSquareSum
          (case2PassiveThetaWithFollowingFactorProductResidualReadout
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e) := by
    simpa [sourceChart] using
      aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_case2PassiveThetaWithFollowingFactorEndpointSourceChart_eq_of_detChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e z hdet_z
  have hread : readback (sourceChart z) = z := hleft z hzV
  simpa [sourceChart, readback,
    case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout,
    hread] using hsq_source

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
