import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalPriorResidualBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage

/-!
# Case 2 with-following original-prior residual rank-cut bridge

This file composes the with-following original-prior residual-integrability
patch with the local source-rank adapter.  It only restricts the already proved
fixed-base residual negative-power predicate to the source-rank cut; it does
not prove residual positivity, source-rank coverage, an original `lossDLN`
comparison, normal crossings, pole order, or RLCT extraction.
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

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Fixed-base residual negative-power integrability restricts to smaller
source sets.

This is only monotonicity of a nonnegative lower integral under restriction of
the measure.  It does not add residual positivity or any loss comparison. -/
theorem residualNegPowerIntegrableOn_mono
    {N : ℕ}
    (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
    [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
    [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
    [∀ i, ContinuousSMul ℝ (W i)]
    (B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc)
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source source' : Set α} {μ : Measure α} {t : ℝ}
    (hsubset : source' ⊆ source)
    (hbase : residualNegPowerIntegrableOn
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t) :
    residualNegPowerIntegrableOn
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source' μ t := by
  exact
    (lintegral_mono'
      (Measure.restrict_mono hsubset le_rfl)
      (le_refl (fun x : α ↦ ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t))))).trans_lt
      (by simpa [residualNegPowerIntegrableOn] using hbase)

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This proof composes two large local Case 2 wrappers and then performs set/measure bookkeeping.
/-- With-following fixed-base residual negative-power integrability on the
rank-cut p.13/readback-preimage patch for the original edge-family prior.

The theta-side rank locus records exactly the two residual-rank equations for
the free following factor and the successor selected-entry matrix.  The theorem
shrinks inside the local rank adapter before applying the original-prior
residual theorem, so the returned rank-cut image equality and the restricted
integrability predicate use the same `V`.  This remains only a local rank-cut
adapter: it does not prove rank-stratum coverage, residual positivity,
original `lossDLN` integrability, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_residualNegPowerIntegrableOn_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_continuousAt_priorDensity_of_subset_detSector
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
                        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                          residualNegPowerIntegrableOn
                            (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                            (fun E : EdgeFamily ↦ E)
                            ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum)
                            (originalEdgeFamilyPrior
                              (V := reverseVertex W₂)
                              (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                              density)
                            t := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet sourceStratum rankEq
  have hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
    hGdet hz₀G
  rcases
      (by
        simpa [Θ, EdgeFamily, p13SourceSet, sourceStratum, rankEq] using
          exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_rankEq_eq_p13SourceEdgeFamilySet_inter_readback_preimage_inter_sourceRankStratum
            (r := r) (rEdge := rEdge)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
            eNext e z₀ hdet₀ hpivot₀ G hGopen hz₀G hprod) with
    ⟨Vrank, hVrank_open, hz₀Vrank, hVrankG, _hdetRank, _hpivotRank,
      _hleftRank, _hsourceInjRank, _hsourceContRank, _hsourceImageRank,
      hiffRank, _himageRank⟩
  have hiffRank' : ∀ z ∈ Vrank, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq := by
    intro z hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ Vrank := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz
    simpa [sourceChart, sourceStratum, rankEq,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hiffRank z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  let Grank : Set Θ := G ∩ Vrank
  have hGrank_open : IsOpen Grank := hGopen.inter hVrank_open
  have hz₀Grank : z₀ ∈ Grank := ⟨hz₀G, hz₀Vrank⟩
  have hGrank_det :
      Grank ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J := by
    intro z hz
    exact hGdet hz.1
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, p13SourceSet] using
          exists_open_residualNegPowerIntegrableOn_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_isOpen_case2PassiveThetaWithFollowingFactor_of_continuousAt_priorDensity_of_subset_detSector
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
            Grank hGrank_open hz₀Grank hGrank_det) with
    ⟨V, hVopen, hz₀V, hVGrank, hleft, hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hresidual_full⟩
  have hVG : V ⊆ G := fun z hz ↦ (hVGrank hz).1
  have hVVrank : V ⊆ Vrank := fun z hz ↦ (hVGrank hz).2
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
  have hsourceStratum_meas : MeasurableSet sourceStratum := by
    simpa [sourceStratum] using
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
        (W := W₂) (B := B₂)
        (Cedge := fun E : EdgeFamily ↦ E) (r := r) (rEdge := rEdge)
        (by simpa [EdgeFamily] using (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
  have hrankPiece_meas :
      MeasurableSet ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) :=
    hpiece_meas.inter hsourceStratum_meas
  have hiffV : ∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq := by
    intro z hz
    exact hiffRank' z (hVVrank hz)
  have himage_rank :
      sourceChart '' (V ∩ rankEq) =
        (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum := by
    ext E
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨hzV, hzrank⟩
      have hzfull : sourceChart z ∈ p13SourceSet ∩ readback ⁻¹' V := by
        rw [← himage]
        exact ⟨z, hzV, rfl⟩
      exact ⟨hzfull, (hiffV z hzV).2 hzrank⟩
    · intro hE
      have hEfull : E ∈ sourceChart '' V := by
        rw [himage]
        exact hE.1
      rcases hEfull with ⟨z, hzV, rfl⟩
      exact ⟨z, ⟨hzV, (hiffV z hzV).1 hE.2⟩, rfl⟩
  refine
    ⟨V, hVopen, hz₀V, hVG, hleft', hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV, himage_rank, ?_⟩
  intro rawHaar hrawHaar
  exact
    residualNegPowerIntegrableOn_mono
      (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EdgeFamily ↦ E)
      (source := p13SourceSet ∩ readback ⁻¹' V)
      (source' := (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum)
      (μ := originalEdgeFamilyPrior
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        density)
      (t := t) Set.inter_subset_left
      (hresidual_full rawHaar)

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This proof reuses a large local Case 2 wrapper and then performs measure-source bookkeeping.
/-- With-following residual source hypotheses on the rank-cut
p.13/readback-preimage patch for the original edge-family prior, conditional
on residual zero-locus nullity there.

This wraps the rank-cut residual-integrability theorem with the generic
zero-locus-nullity-to-a.e.-positivity handoff.  The nullity hypothesis is on
the restricted original prior over the same rank-cut source set; the theorem
does not prove that nullity, source-rank coverage, an original `lossDLN`
comparison, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_continuousAt_priorDensity_of_subset_detSector
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
                        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                          ((originalEdgeFamilyPrior
                              (V := reverseVertex W₂)
                              (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                              density).restrict
                            ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum))
                            {E | aoyagiCoordinateSquareSum
                              (paperEndpointFixedBaseResidualBlockCoordinateMap
                                (K := ℝ) W₂ B₂ U₀ hU₀
                                (fun E : EdgeFamily ↦ E) E) = 0} = 0 →
                            (∀ᵐ E ∂ (originalEdgeFamilyPrior
                                (V := reverseVertex W₂)
                                (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                density).restrict
                              ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
                                0 < aoyagiCoordinateSquareSum
                                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                                    (K := ℝ) W₂ B₂ U₀ hU₀
                                    (fun E : EdgeFamily ↦ E) E)) ∧
                              residualNegPowerIntegrableOn
                                (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                                (fun E : EdgeFamily ↦ E)
                                ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum)
                                (originalEdgeFamilyPrior
                                  (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density)
                                t := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet sourceStratum rankEq
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, p13SourceSet, sourceStratum, rankEq] using
          exists_open_residualNegPowerIntegrableOn_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_continuousAt_priorDensity_of_subset_detSector
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
            G hGopen hz₀G hGdet (r := r) (rEdge := rEdge) hprod) with
    ⟨V, hVopen, hz₀V, hVG, hleft, hsource_inj, hsource_contOn,
      hpiece_meas, hpiece_open, himage, hrankPiece_meas, hiffV,
      himage_rank, hresidual_rank⟩
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
  intro rawHaar hrawHaar hzero
  exact
    residualSourceHypotheses_mono_of_zero_set_null
      (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := fun E : EdgeFamily ↦ E)
      (source := (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum)
      (source' := (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum)
      (μ := originalEdgeFamilyPrior
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        density)
      (t := t)
      (by intro E hE; exact hE)
      hzero
      (hresidual_rank rawHaar)

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
