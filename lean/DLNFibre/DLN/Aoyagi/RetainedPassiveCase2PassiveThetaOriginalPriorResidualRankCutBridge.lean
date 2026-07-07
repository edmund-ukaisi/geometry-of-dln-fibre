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

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- Rank-cut original-prior residual zero-locus nullity from readback
domination and theta-side product-residual positivity.

This is only the exact Aoyagi-specialized socket for the rank-cut source.  The
readback domination, theta-side positivity, and zero-locus implication are
still explicit inputs. -/
theorem originalEdgeFamilyPrior_rankCut_residual_zero_set_eq_zero_of_readback_map_le_smul_productResidual_pos_ae
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)]
    [∀ i, Module ℝ (W₂ i)]
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
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    {priorDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ}
    {r : ℕ} {rEdge : Fin 2 → ℕ}
    (V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    {coordinateSourceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)}
    {c : ℝ≥0∞} :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankCutSource : Set EdgeFamily :=
      (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
    let μprior : Measure EdgeFamily :=
      originalEdgeFamilyPrior
        (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
        priorDensity
    let fixedResidual : EdgeFamily → ℝ := fun E ↦
      aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)
    let productResidual : Θ → ℝ := fun z ↦
      aoyagiCoordinateSquareSum
        (case2PassiveThetaWithFollowingFactorProductResidualReadout
          n hS hcont hnext z eNext e)
    AEMeasurable readback (μprior.restrict rankCutSource) →
    Measure.map readback (μprior.restrict rankCutSource) ≤
      c • coordinateSourceMeasure.restrict V →
    (∀ᵐ z ∂ coordinateSourceMeasure.restrict V, 0 < productResidual z) →
    {E | fixedResidual E = 0} ≤ᵐ[μprior.restrict rankCutSource]
      readback ⁻¹' {z | productResidual z = 0} →
    (μprior.restrict rankCutSource) {E | fixedResidual E = 0} = 0 := by
  intro Θ EdgeFamily readback p13SourceSet sourceStratum rankCutSource μprior
    fixedResidual productResidual hread hmap hpos hzero_imp
  exact
    measure_zero_set_eq_zero_of_map_le_smul_of_ae_pos_of_ae_zero_imp
      (μ := μprior.restrict rankCutSource)
      (θμ := coordinateSourceMeasure.restrict V)
      (c := c)
      (readback := readback)
      (f := fixedResidual)
      (g := productResidual)
      hread hmap hpos hzero_imp

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- Source-image residual equality gives the a.e. zero-locus implication
needed by the readback zero-locus handoff.

The statement is deliberately measure/set theoretic: the Aoyagi-specific
residual equality is supplied as `hsq`, so this helper does not force Lean to
normalize the large Case 2 coordinate types. -/
theorem zero_set_ae_le_readback_preimage_zero_set_of_source_subset_image
    {Θ E : Type*} [MeasurableSpace E] {μ : Measure E}
    {V : Set Θ} {source : Set E}
    {sourceChart : Θ → E} {readback : E → Θ}
    {f : E → ℝ} {g : Θ → ℝ}
    (hsource_meas : MeasurableSet source)
    (hsource_image : source ⊆ sourceChart '' V)
    (hleft : ∀ z ∈ V, readback (sourceChart z) = z)
    (hsq : ∀ z ∈ V, f (sourceChart z) = g z) :
    {E | f E = 0} ≤ᵐ[μ.restrict source] readback ⁻¹' {z | g z = 0} := by
  filter_upwards [ae_restrict_mem hsource_meas] with E hE hEzero
  rcases hsource_image hE with ⟨z, hzV, rfl⟩
  have hg_zero : g z = 0 := by
    rw [← hsq z hzV]
    exact hEzero
  change g (readback (sourceChart z)) = 0
  rw [hleft z hzV]
  exact hg_zero

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

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This proof composes the zero-set readback socket with the existing residual-source wrapper.
/-- With-following residual source hypotheses on the rank-cut
p.13/readback-preimage patch, using readback domination and theta-side
product-residual positivity instead of an explicit zero-locus-nullity input.

The theorem still keeps the actual readback domination, theta-side positivity,
and zero-locus implication as inputs to the returned continuation.  It does
not prove prior transport, determinant/raw Haar transport, residual equality,
source-rank coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_readback_map_le_smul_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
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
                          let rankCutSource : Set EdgeFamily :=
                            (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
                          let μprior : Measure EdgeFamily :=
                            originalEdgeFamilyPrior
                              (V := reverseVertex W₂)
                              (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                              density
                          let fixedResidual : EdgeFamily → ℝ := fun E ↦
                            aoyagiCoordinateSquareSum
                              (paperEndpointFixedBaseResidualBlockCoordinateMap
                                (K := ℝ) W₂ B₂ U₀ hU₀
                                (fun E : EdgeFamily ↦ E) E)
                          let productResidual : Θ → ℝ := fun z ↦
                            aoyagiCoordinateSquareSum
                              (case2PassiveThetaWithFollowingFactorProductResidualReadout
                                n hS hcont hnext z eNext e)
                          ∀ (coordinateSourceMeasure : Measure Θ) (Cread : ℝ≥0∞),
                            AEMeasurable readback (μprior.restrict rankCutSource) →
                            Measure.map readback (μprior.restrict rankCutSource) ≤
                              Cread • coordinateSourceMeasure.restrict V →
                            (∀ᵐ z ∂ coordinateSourceMeasure.restrict V,
                              0 < productResidual z) →
                            (∀ᵐ E ∂ μprior.restrict rankCutSource,
                              0 < fixedResidual E) ∧
                              residualNegPowerIntegrableOn
                                (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                                (fun E : EdgeFamily ↦ E)
                                rankCutSource μprior t := by
  intro Θ RawTuple EdgeFamily sourceChart readback p13SourceSet sourceStratum rankEq
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, p13SourceSet, sourceStratum, rankEq] using
          exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_continuousAt_priorDensity_of_subset_detSector
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
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
  intro rawHaar hrawHaar
  dsimp only
  intro coordinateSourceMeasure Cread hread hread_map_le hproductResidual_pos_ae
  let rankCutSource : Set EdgeFamily :=
    (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
  let μprior : Measure EdgeFamily :=
    originalEdgeFamilyPrior
      (V := reverseVertex W₂)
      (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
      density
  let fixedResidual : EdgeFamily → ℝ := fun E ↦
    aoyagiCoordinateSquareSum
      (paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)
  let productResidual : Θ → ℝ := fun z ↦
    aoyagiCoordinateSquareSum
      (case2PassiveThetaWithFollowingFactorProductResidualReadout
        n hS hcont hnext z eNext e)
  have hsource_subset_image : rankCutSource ⊆ sourceChart '' V := by
    intro E hE
    rw [himage]
    exact hE.1
  have hsq : ∀ z ∈ V, fixedResidual (sourceChart z) = productResidual z := by
    intro z hzV
    have hdet_z :
        (case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e).detChart := by
      exact
        case2PassiveThetaWithFollowingFactorEndpointRetainedData_detChart
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
          (hGdet (hVG hzV))
    simpa [sourceChart, fixedResidual, productResidual] using
      aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_case2PassiveThetaWithFollowingFactorEndpointSourceChart_eq_of_detChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e z hdet_z
  have hfixed_zero_imp_product_zero_ae :
      {E | fixedResidual E = 0} ≤ᵐ[μprior.restrict rankCutSource]
        readback ⁻¹' {z | productResidual z = 0} :=
    zero_set_ae_le_readback_preimage_zero_set_of_source_subset_image
      (μ := μprior) (V := V) (source := rankCutSource)
      (sourceChart := sourceChart) (readback := readback)
      (f := fixedResidual) (g := productResidual)
      hrankPiece_meas hsource_subset_image hleft' hsq
  have hzero :
      (μprior.restrict rankCutSource) {E | fixedResidual E = 0} = 0 := by
    simpa [rankCutSource, μprior, fixedResidual, productResidual] using
      originalEdgeFamilyPrior_rankCut_residual_zero_set_eq_zero_of_readback_map_le_smul_productResidual_pos_ae
        (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
        (U₀ := U₀) (hU₀ := hU₀) eNext e
        (priorDensity := density) (r := r) (rEdge := rEdge) V
        (coordinateSourceMeasure := coordinateSourceMeasure) (c := Cread)
        hread hread_map_le hproductResidual_pos_ae hfixed_zero_imp_product_zero_ae
  simpa [rankCutSource, μprior, fixedResidual] using
    hresidual_source rawHaar hzero

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This proof composes same-shrink prior readback domination with the rank-cut residual-source wrapper.
/-- Rank-cut residual source hypotheses from endpoint-reference prior
readback domination and theta-side product-residual positivity.

The theorem returns an outer shrink `W`, where the endpoint-reference
weighted-Haar identity, endpoint lower bound, source-density lower bound, and
prior-density upper bound are stated, and an inner rank-cut shrink `V`, where
the residual-source conclusion lives.  It still does not prove determinant/raw
Haar transport, source-prior transport, the density bounds, theta-side
positivity, source-rank coverage, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
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
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure : Measure Θ :=
      baseJ.withDensity sourceDensity
    let rawMap : Θ → RawTuple :=
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
    let endpointJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
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
    let originalVolume : Measure EdgeFamily :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    ∃ W : Set Θ,
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ G ∧
        ∃ V : Set Θ,
          IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
            (∀ z ∈ V, readback (sourceChart z) = z) ∧
              Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
                  IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                    sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                      MeasurableSet
                        ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                        (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                          sourceChart '' (V ∩ rankEq) =
                            (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                            ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                              let rankCutSource : Set EdgeFamily :=
                                (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
                              let μprior : Measure EdgeFamily :=
                                originalEdgeFamilyPrior
                                  (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density
                              let fixedResidual : EdgeFamily → ℝ := fun E ↦
                                aoyagiCoordinateSquareSum
                                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                                    (K := ℝ) W₂ B₂ U₀ hU₀
                                    (fun E : EdgeFamily ↦ E) E)
                              let productResidual : Θ → ℝ := fun z ↦
                                aoyagiCoordinateSquareSum
                                  (case2PassiveThetaWithFollowingFactorProductResidualReadout
                                    n hS hcont hnext z eNext e)
                              ∀ {Cdet ε : ℝ≥0∞},
                                let P : Set RawTuple :=
                                  rawSourceSet ∩ rawChart ⁻¹' rankCutSource
                                let endpointReferenceImage : Measure RawTuple :=
                                  case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                                    (κ' := throughSubspaceEndpointComplementIndex
                                      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                                    n hS hcont hnext eNext e Rres W
                                endpointReferenceImage =
                                    (rawHaar.restrict
                                      (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P)).withDensity
                                      endpointJacobianDensity →
                                  Cdet < ∞ →
                                    (∀ᵐ y ∂rawHaar.restrict
                                        (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P),
                                      1 ≤ Cdet * endpointJacobianDensity y) →
                                      (∀ᵐ z ∂baseJ.restrict W, ε ≤ sourceDensity z) →
                                        ε ≠ 0 →
                                          ε ≠ ∞ →
                                            ∀ {Kprior : ℝ},
                                              (∀ᵐ E ∂ originalVolume.restrict rankCutSource,
                                                density E ≤ Kprior) →
                                                (∀ᵐ z ∂coordinateSourceMeasure.restrict V,
                                                  0 < productResidual z) →
                                                  let cHaar :=
                                                    ((Measure.map
                                                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                                        W₂ B₂ U₀)
                                                      rawHaar).addHaarScalarFactor
                                                        (originalTupleVolume d))
                                                  let Ddet := Cdet * ε⁻¹
                                                  let Dvol :=
                                                    (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                                  let Cprior := ENNReal.ofReal Kprior * Dvol
                                                  Cprior < ∞ ∧
                                                    (∀ᵐ E ∂μprior.restrict rankCutSource,
                                                      0 < fixedResidual E) ∧
                                                      residualNegPowerIntegrableOn
                                                        (W := W₂) (B := B₂) (U₀ := U₀)
                                                        (hU₀ := hU₀)
                                                        (fun E : EdgeFamily ↦ E)
                                                        rankCutSource μprior t := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart endpointJacobianDensity rawSourceSet
    p13SourceSet rawChart d originalVolume sourceStratum rankEq
  have hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
    hGdet hz₀G
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawMap, rawOrderOnEndpoint, rawDetChart, endpointJacobianDensity,
          rawSourceSet, p13SourceSet, rawChart, d, originalVolume] using
          exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_same_shrink_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper
            W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hdet₀ hpivot₀
            sourceImageDensity Rres G hGopen hz₀G) with
    ⟨W, hWopen, hz₀W, hWG, _hleftW, _hsource_injW, _hsource_contOnW,
      _hsource_imageW, _himage_p13W, hprior_package⟩
  have hWdet :
      W ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J := fun z hzW ↦
    hGdet (hWG hzW)
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, sourceChart, readback,
          p13SourceSet, sourceStratum, rankEq] using
          exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_readback_map_le_smul_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
            W hWopen hz₀W hWdet (r := r) (rEdge := rEdge) hprod) with
    ⟨V, hVopen, hz₀V, hVW, hleftV, hsource_injV, hsource_contOnV,
      hpiece_meas, hpiece_open, himageV, hrankPiece_meas, hiffV,
      himage_rank, hresidual_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
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
    ⟨W, hWopen, hz₀W, hWG, V, hVopen, hz₀V, hVW, hleftV',
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV', himage_rank, ?_⟩
  intro rawHaar hrawHaar rankCutSource μprior fixedResidual productResidual Cdet ε P
    endpointReferenceImage
    hendpoint hCdet
    hendpoint_lower hsource_lower hε_ne_zero hε_ne_top Kprior
    hprior_upper hproductResidual_pos_ae cHaar Ddet Dvol Cprior
  have hrankCut_subset_V : rankCutSource ⊆ sourceChart '' V := by
    intro E hE
    rw [himageV]
    exact hE.1
  have hrankCut_subset_W : rankCutSource ⊆ sourceChart '' W := by
    intro E hE
    rcases hrankCut_subset_V hE with ⟨z, hzV, rfl⟩
    exact ⟨z, hVW hzV, rfl⟩
  have hrankCut_subset_V_concrete :
      rankCutSource ⊆
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e) '' V := by
    simpa [sourceChart] using hrankCut_subset_V
  have hleftV_concrete :
      ∀ z ∈ V,
        case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
            W₂ B₂ n hS hnext hU₀ e
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z) = z := by
    simpa [sourceChart, readback] using hleftV'
  have hV_meas : MeasurableSet V := hVopen.measurableSet
  rcases
      (by
        simpa [rankCutSource, P, endpointReferenceImage, d, originalVolume,
          cHaar, Ddet, Dvol, Cprior] using
          hprior_package rawHaar rankCutSource (Cdet := Cdet) (ε := ε)
            hrankPiece_meas hrankCut_subset_W hendpoint hCdet
            hendpoint_lower hsource_lower hε_ne_zero hε_ne_top
            (density := density) (Kprior := Kprior) hprior_upper) with
    ⟨hCprior, hread, hmapW⟩
  have hmapV_concrete :
      Measure.map
          (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
            W₂ B₂ n hS hnext hU₀ e)
          (μprior.restrict rankCutSource) ≤
        Cprior • coordinateSourceMeasure.restrict V := by
    simpa [rankCutSource, μprior] using
      measure_map_restrict_source_subset_image_le_smul_restrict_of_le_smul_restrict_superset
        (Θ := Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
        (E := EdgeFamily)
        (source := rankCutSource) (V := V) (G := W)
        (sourceChart :=
          case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (readback :=
          case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
            W₂ B₂ n hS hnext hU₀ e)
        (μ := μprior) (θμ := coordinateSourceMeasure) (c := Cprior)
        hrankPiece_meas hV_meas hrankCut_subset_V_concrete
        hleftV_concrete hVW
        (by simpa [rankCutSource, μprior, readback] using hread)
        (by simpa [rankCutSource, μprior, Cprior, readback] using hmapW)
  have hresidual :
      (∀ᵐ E ∂μprior.restrict rankCutSource,
        0 <
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
        residualNegPowerIntegrableOn
          (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
          (fun E : EdgeFamily ↦ E) rankCutSource μprior t := by
    simpa [rankCutSource, μprior] using
      hresidual_package rawHaar coordinateSourceMeasure Cprior
        (by simpa [rankCutSource, μprior] using hread)
        (by simpa [rankCutSource, μprior, readback] using hmapV_concrete)
        (by simpa [rankCutSource] using hproductResidual_pos_ae)
  simpa [rankCutSource, μprior] using ⟨hCprior, hresidual⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This proof replaces endpoint-reference equality by active endpoint-patch containment.
/-- Rank-cut residual source hypotheses from active endpoint-patch containment.

The theorem returns an outer shrink `W`, where the active endpoint-patch
containment, source-density lower bound, and prior-density upper bound are
stated, and an inner rank-cut shrink `V`, where the residual-source conclusion
lives.  The determinant constant is produced by the active-containment prior
readback adapter.  This remains only support and measure-comparison
bookkeeping: it does not prove active containment, determinant/raw Haar
transport, source-prior transport, the density bounds, theta-side positivity,
source-rank coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
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
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure : Measure Θ :=
      baseJ.withDensity sourceDensity
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
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume : Measure EdgeFamily :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    ∃ W : Set Θ,
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ G ∧
        ∃ V : Set Θ,
          IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
            (∀ z ∈ V, readback (sourceChart z) = z) ∧
              Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
                  IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                    sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                      MeasurableSet
                        ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                        (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                          sourceChart '' (V ∩ rankEq) =
                            (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                            ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                              let rankCutSource : Set EdgeFamily :=
                                (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
                              let μprior : Measure EdgeFamily :=
                                originalEdgeFamilyPrior
                                  (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density
                              let fixedResidual : EdgeFamily → ℝ := fun E ↦
                                aoyagiCoordinateSquareSum
                                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                                    (K := ℝ) W₂ B₂ U₀ hU₀
                                    (fun E : EdgeFamily ↦ E) E)
                              let productResidual : Θ → ℝ := fun z ↦
                                aoyagiCoordinateSquareSum
                                  (case2PassiveThetaWithFollowingFactorProductResidualReadout
                                    n hS hcont hnext z eNext e)
                              ∀ {ε : ℝ≥0∞},
                                let P : Set RawTuple :=
                                  rawSourceSet ∩ rawChart ⁻¹' rankCutSource
                                let endpointPatch : Set RawTuple :=
                                  rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P
                                let activePatchImage := activeChart '' (W ∩ sourceCylinder)
                                endpointPatch ⊆ activeWriteback '' activePatchImage →
                                  (∀ᵐ z ∂baseJ.restrict W, ε ≤ sourceDensity z) →
                                    ε ≠ 0 →
                                      ε ≠ ∞ →
                                        ∀ {Kprior : ℝ},
                                          (∀ᵐ E ∂ originalVolume.restrict rankCutSource,
                                            density E ≤ Kprior) →
                                            (∀ᵐ z ∂coordinateSourceMeasure.restrict V,
                                              0 < productResidual z) →
                                              ∃ Cdet : ℝ≥0∞,
                                                Cdet < ∞ ∧
                                                  let cHaar :=
                                                    ((Measure.map
                                                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                                        W₂ B₂ U₀)
                                                      rawHaar).addHaarScalarFactor
                                                        (originalTupleVolume d))
                                                  let Ddet := Cdet * ε⁻¹
                                                  let Dvol :=
                                                    (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                                  let Cprior := ENNReal.ofReal Kprior * Dvol
                                                  Cprior < ∞ ∧
                                                    (∀ᵐ E ∂μprior.restrict rankCutSource,
                                                      0 < fixedResidual E) ∧
                                                      residualNegPowerIntegrableOn
                                                        (W := W₂) (B := B₂) (U₀ := U₀)
                                                        (hU₀ := hU₀)
                                                        (fun E : EdgeFamily ↦ E)
                                                        rankCutSource μprior t := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawOrderOnEndpoint
    rawDetChart rawSourceSet p13SourceSet rawChart d originalVolume pivotNext
    signedBox sourceCylinder activeChart activeWriteback sourceStratum rankEq
  have hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
    hGdet hz₀G
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet, rawChart,
          d, originalVolume, pivotNext, signedBox, sourceCylinder, activeChart,
          activeWriteback] using
          exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_same_shrink_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower_priorDensity_upper
            W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hdet₀ hpivot₀
            sourceImageDensity Rres G hGopen hz₀G) with
    ⟨W, hWopen, hz₀W, hWG, _hleftW, _hsource_injW, _hsource_contOnW,
      _hsource_imageW, _himage_p13W, hprior_package⟩
  have hWdet :
      W ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J := fun z hzW ↦
    hGdet (hWG hzW)
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, sourceChart, readback,
          p13SourceSet, sourceStratum, rankEq] using
          exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_readback_map_le_smul_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
            W hWopen hz₀W hWdet (r := r) (rEdge := rEdge) hprod) with
    ⟨V, hVopen, hz₀V, hVW, hleftV, hsource_injV, hsource_contOnV,
      hpiece_meas, hpiece_open, himageV, hrankPiece_meas, hiffV,
      himage_rank, hresidual_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
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
    ⟨W, hWopen, hz₀W, hWG, V, hVopen, hz₀V, hVW, hleftV',
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV', himage_rank, ?_⟩
  intro rawHaar hrawHaar rankCutSource μprior fixedResidual productResidual ε P
    endpointPatch activePatchImage hpatch hsource_lower hε_ne_zero hε_ne_top
    Kprior hprior_upper hproductResidual_pos_ae
  have hrankCut_subset_V : rankCutSource ⊆ sourceChart '' V := by
    intro E hE
    rw [himageV]
    exact hE.1
  have hrankCut_subset_W : rankCutSource ⊆ sourceChart '' W := by
    intro E hE
    rcases hrankCut_subset_V hE with ⟨z, hzV, rfl⟩
    exact ⟨z, hVW hzV, rfl⟩
  have hrankCut_subset_V_concrete :
      rankCutSource ⊆
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e) '' V := by
    simpa [sourceChart] using hrankCut_subset_V
  have hleftV_concrete :
      ∀ z ∈ V,
        case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
            W₂ B₂ n hS hnext hU₀ e
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z) = z := by
    simpa [sourceChart, readback] using hleftV'
  have hV_meas : MeasurableSet V := hVopen.measurableSet
  rcases
      (by
        simpa [rankCutSource, P, endpointPatch, activePatchImage, d,
          originalVolume] using
          hprior_package rawHaar rankCutSource (ε := ε)
            hrankPiece_meas hrankCut_subset_W hpatch hsource_lower
            hε_ne_zero hε_ne_top (density := density) (Kprior := Kprior)
            hprior_upper) with
    ⟨Cdet, hCdet, hCprior, hread, hmapW⟩
  have hmapV_concrete :
      Measure.map
          (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
            W₂ B₂ n hS hnext hU₀ e)
          (μprior.restrict rankCutSource) ≤
        (let cHaar :=
          ((Measure.map
            (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
              W₂ B₂ U₀) rawHaar).addHaarScalarFactor (originalTupleVolume d))
         let Ddet := Cdet * ε⁻¹
         let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
         let Cprior := ENNReal.ofReal Kprior * Dvol
         Cprior) • coordinateSourceMeasure.restrict V := by
    simpa [rankCutSource, μprior] using
      measure_map_restrict_source_subset_image_le_smul_restrict_of_le_smul_restrict_superset
        (Θ := Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
        (E := EdgeFamily)
        (source := rankCutSource) (V := V) (G := W)
        (sourceChart :=
          case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (readback :=
          case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
            W₂ B₂ n hS hnext hU₀ e)
        (μ := μprior) (θμ := coordinateSourceMeasure)
        (c :=
          let cHaar :=
            ((Measure.map
              (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                W₂ B₂ U₀) rawHaar).addHaarScalarFactor (originalTupleVolume d))
          let Ddet := Cdet * ε⁻¹
          let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
          ENNReal.ofReal Kprior * Dvol)
        hrankPiece_meas hV_meas hrankCut_subset_V_concrete
        hleftV_concrete hVW
        (by simpa [rankCutSource, μprior, readback] using hread)
        (by simpa [rankCutSource, μprior, readback] using hmapW)
  have hresidual :
      (∀ᵐ E ∂μprior.restrict rankCutSource,
        0 <
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
        residualNegPowerIntegrableOn
          (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
          (fun E : EdgeFamily ↦ E) rankCutSource μprior t := by
    simpa [rankCutSource, μprior] using
      hresidual_package rawHaar coordinateSourceMeasure
        (let cHaar :=
          ((Measure.map
            (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
              W₂ B₂ U₀) rawHaar).addHaarScalarFactor (originalTupleVolume d))
         let Ddet := Cdet * ε⁻¹
         let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
         ENNReal.ofReal Kprior * Dvol)
        (by simpa [rankCutSource, μprior] using hread)
        (by simpa [rankCutSource, μprior, readback] using hmapV_concrete)
        (by simpa [rankCutSource] using hproductResidual_pos_ae)
  refine ⟨Cdet, hCdet, ?_⟩
  simpa [rankCutSource, μprior, fixedResidual] using ⟨hCprior, hresidual⟩

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Replaces active containment by source-cylinder support for the rank-cut source.
/-- Rank-cut residual source hypotheses from source-cylinder support, source-density
lower bound, prior-density upper bound, and theta-side product-residual positivity.

The theorem returns an outer shrink `W` and an inner rank-cut shrink `V`.  The
terminal support socket is the chart-piece containment
`rankCutSource ⊆ sourceChart '' (W ∩ sourceCylinder)`.  The existing
source-cylinder prior readback package proves the active endpoint containment
internally, then support bookkeeping sharpens the readback domination from the
ambient source neighborhood to the inner rank-cut shrink.

This remains conditional support and measure-comparison bookkeeping.  It does
not prove source-cylinder support for the rank-cut source, source-density
positivity, prior-density upper bounds, determinant/raw Haar transport,
source-prior transport, source-rank coverage, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_rankCutSource_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
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
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure : Measure Θ :=
      baseJ.withDensity sourceDensity
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
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume : Measure EdgeFamily :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    ∃ W : Set Θ,
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ G ∧
        ∃ V : Set Θ,
          IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
            (∀ z ∈ V, readback (sourceChart z) = z) ∧
              Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
                  IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                    sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                      MeasurableSet
                        ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                        (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                          sourceChart '' (V ∩ rankEq) =
                            (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                            ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                              let rankCutSource : Set EdgeFamily :=
                                (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
                              let μprior : Measure EdgeFamily :=
                                originalEdgeFamilyPrior
                                  (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density
                              let fixedResidual : EdgeFamily → ℝ := fun E ↦
                                aoyagiCoordinateSquareSum
                                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                                    (K := ℝ) W₂ B₂ U₀ hU₀
                                    (fun E : EdgeFamily ↦ E) E)
                              let productResidual : Θ → ℝ := fun z ↦
                                aoyagiCoordinateSquareSum
                                  (case2PassiveThetaWithFollowingFactorProductResidualReadout
                                    n hS hcont hnext z eNext e)
                              ∀ {ε : ℝ≥0∞},
                                rankCutSource ⊆ sourceChart '' (W ∩ sourceCylinder) →
                                  (∀ᵐ z ∂baseJ.restrict W, ε ≤ sourceDensity z) →
                                    ε ≠ 0 →
                                      ε ≠ ∞ →
                                        ∀ {Kprior : ℝ},
                                          (∀ᵐ E ∂ originalVolume.restrict rankCutSource,
                                            density E ≤ Kprior) →
                                            (∀ᵐ z ∂coordinateSourceMeasure.restrict V,
                                              0 < productResidual z) →
                                              ∃ Cdet : ℝ≥0∞,
                                                Cdet < ∞ ∧
                                                  let cHaar :=
                                                    ((Measure.map
                                                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                                        W₂ B₂ U₀)
                                                      rawHaar).addHaarScalarFactor
                                                        (originalTupleVolume d))
                                                  let Ddet := Cdet * ε⁻¹
                                                  let Dvol :=
                                                    (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                                  let Cprior := ENNReal.ofReal Kprior * Dvol
                                                  Cprior < ∞ ∧
                                                    (∀ᵐ E ∂μprior.restrict rankCutSource,
                                                      0 < fixedResidual E) ∧
                                                      residualNegPowerIntegrableOn
                                                        (W := W₂) (B := B₂) (U₀ := U₀)
                                                        (hU₀ := hU₀)
                                                        (fun E : EdgeFamily ↦ E)
                                                        rankCutSource μprior t := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawOrderOnEndpoint
    rawDetChart rawSourceSet p13SourceSet rawChart d originalVolume pivotNext
    signedBox sourceCylinder activeChart activeWriteback sourceStratum rankEq
  have hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
    hGdet hz₀G
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet, rawChart,
          d, originalVolume, pivotNext, signedBox, sourceCylinder, activeChart,
          activeWriteback] using
          exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower_priorDensity_upper
            W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hdet₀ hpivot₀
            sourceImageDensity Rres G hGopen hz₀G) with
    ⟨W, hWopen, hz₀W, hWG, _hleftW, _hsource_injW, _hsource_contOnW,
      _hsource_imageW, _himage_p13W, hprior_package⟩
  have hWdet :
      W ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J := fun z hzW ↦
    hGdet (hWG hzW)
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, sourceChart, readback,
          p13SourceSet, sourceStratum, rankEq] using
          exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_inter_sourceRankStratum_case2PassiveThetaWithFollowingFactor_of_readback_map_le_smul_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
            (τ := τ) W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
            W hWopen hz₀W hWdet (r := r) (rEdge := rEdge) hprod) with
    ⟨V, hVopen, hz₀V, hVW, hleftV, hsource_injV, hsource_contOnV,
      hpiece_meas, hpiece_open, himageV, hrankPiece_meas, hiffV,
      himage_rank, hresidual_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
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
    ⟨W, hWopen, hz₀W, hWG, V, hVopen, hz₀V, hVW, hleftV',
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV', himage_rank, ?_⟩
  intro rawHaar hrawHaar rankCutSource μprior fixedResidual productResidual ε
    hrankCut_subset_sourceCylinder hsource_lower hε_ne_zero hε_ne_top
    Kprior hprior_upper hproductResidual_pos_ae
  have hrankCut_subset_V : rankCutSource ⊆ sourceChart '' V := by
    intro E hE
    rw [himageV]
    exact hE.1
  have hrankCut_subset_W : rankCutSource ⊆ sourceChart '' W := by
    intro E hE
    rcases hrankCut_subset_V hE with ⟨z, hzV, rfl⟩
    exact ⟨z, hVW hzV, rfl⟩
  have hrankCut_subset_V_concrete :
      rankCutSource ⊆
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e) '' V := by
    simpa [sourceChart] using hrankCut_subset_V
  have hleftV_concrete :
      ∀ z ∈ V,
        case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
            W₂ B₂ n hS hnext hU₀ e
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z) = z := by
    simpa [sourceChart, readback] using hleftV'
  have hV_meas : MeasurableSet V := hVopen.measurableSet
  have hVG : V ⊆ G := fun z hz ↦ hWG (hVW hz)
  rcases
      (by
        simpa [rankCutSource, d, originalVolume] using
          hprior_package rawHaar rankCutSource (ε := ε)
            hrankPiece_meas hrankCut_subset_sourceCylinder hsource_lower
            hε_ne_zero hε_ne_top (density := density) (Kprior := Kprior)
            hprior_upper) with
    ⟨Cdet, hCdet, hCprior, hread, hmapG⟩
  have hmapV_concrete :
      Measure.map
          (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
            W₂ B₂ n hS hnext hU₀ e)
          (μprior.restrict rankCutSource) ≤
        (let cHaar :=
          ((Measure.map
            (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
              W₂ B₂ U₀) rawHaar).addHaarScalarFactor (originalTupleVolume d))
         let Ddet := Cdet * ε⁻¹
         let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
         let Cprior := ENNReal.ofReal Kprior * Dvol
         Cprior) • coordinateSourceMeasure.restrict V := by
    simpa [rankCutSource, μprior] using
      measure_map_restrict_source_subset_image_le_smul_restrict_of_le_smul_restrict_superset
        (Θ := Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
        (E := EdgeFamily)
        (source := rankCutSource) (V := V) (G := G)
        (sourceChart :=
          case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e)
        (readback :=
          case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
            W₂ B₂ n hS hnext hU₀ e)
        (μ := μprior) (θμ := coordinateSourceMeasure)
        (c :=
          let cHaar :=
            ((Measure.map
              (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                W₂ B₂ U₀) rawHaar).addHaarScalarFactor (originalTupleVolume d))
          let Ddet := Cdet * ε⁻¹
          let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
          ENNReal.ofReal Kprior * Dvol)
        hrankPiece_meas hV_meas hrankCut_subset_V_concrete
        hleftV_concrete hVG
        (by simpa [rankCutSource, μprior, readback] using hread)
        (by simpa [rankCutSource, μprior, readback] using hmapG)
  have hresidual :
      (∀ᵐ E ∂μprior.restrict rankCutSource,
        0 <
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
        residualNegPowerIntegrableOn
          (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
          (fun E : EdgeFamily ↦ E) rankCutSource μprior t := by
    simpa [rankCutSource, μprior] using
      hresidual_package rawHaar coordinateSourceMeasure
        (let cHaar :=
          ((Measure.map
            (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
              W₂ B₂ U₀) rawHaar).addHaarScalarFactor (originalTupleVolume d))
         let Ddet := Cdet * ε⁻¹
         let Dvol := (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
         ENNReal.ofReal Kprior * Dvol)
        (by simpa [rankCutSource, μprior] using hread)
        (by simpa [rankCutSource, μprior, readback] using hmapV_concrete)
        (by simpa [rankCutSource] using hproductResidual_pos_ae)
  refine ⟨Cdet, hCdet, ?_⟩
  simpa [rankCutSource, μprior, fixedResidual] using ⟨hCprior, hresidual⟩


set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Derives source-cylinder support from C-one signed-box support on the rank-cut source.
/-- Rank-cut residual source hypotheses from C-one signed-box support, source-density
lower bound, prior-density upper bound, and theta-side product-residual positivity.

The rank-cut image equality gives `rankCutSource ⊆ sourceChart '' V`.  The
local left inverse identifies the C-one readout of a chart-produced edge family
with the theta coordinate `z.1.yNext`, so pointwise C-one signed-box support on
`rankCutSource` gives source-cylinder support over `V`.  Since `V ⊆ W`, this
feeds the source-cylinder rank-cut residual-source bridge.

This remains conditional support and measure-comparison bookkeeping.  It does
not prove the C-one signed-box support itself, source-density positivity, prior
density bounds, determinant/raw Haar transport, source-prior transport,
source-rank coverage, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_rankCutSource_cOneReadout_mem_signedBox_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
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
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let cOneReadout : EdgeFamily → Case2PassiveTheta.Center n S J → ℝ :=
      case2PassiveThetaWithFollowingFactorEndpointCOneReadout
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure : Measure Θ :=
      baseJ.withDensity sourceDensity
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
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume : Measure EdgeFamily :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    ∃ W : Set Θ,
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ G ∧
        ∃ V : Set Θ,
          IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
            (∀ z ∈ V, readback (sourceChart z) = z) ∧
              Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
                  IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                    sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                      MeasurableSet
                        ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                        (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                          sourceChart '' (V ∩ rankEq) =
                            (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                            ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                              let rankCutSource : Set EdgeFamily :=
                                (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
                              let μprior : Measure EdgeFamily :=
                                originalEdgeFamilyPrior
                                  (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density
                              let fixedResidual : EdgeFamily → ℝ := fun E ↦
                                aoyagiCoordinateSquareSum
                                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                                    (K := ℝ) W₂ B₂ U₀ hU₀
                                    (fun E : EdgeFamily ↦ E) E)
                              let productResidual : Θ → ℝ := fun z ↦
                                aoyagiCoordinateSquareSum
                                  (case2PassiveThetaWithFollowingFactorProductResidualReadout
                                    n hS hcont hnext z eNext e)
                              ∀ {ε : ℝ≥0∞},
                                (∀ E ∈ rankCutSource, cOneReadout E ∈ signedBox) →
                                  (∀ᵐ z ∂baseJ.restrict W, ε ≤ sourceDensity z) →
                                    ε ≠ 0 →
                                      ε ≠ ∞ →
                                        ∀ {Kprior : ℝ},
                                          (∀ᵐ E ∂ originalVolume.restrict rankCutSource,
                                            density E ≤ Kprior) →
                                            (∀ᵐ z ∂coordinateSourceMeasure.restrict V,
                                              0 < productResidual z) →
                                              ∃ Cdet : ℝ≥0∞,
                                                Cdet < ∞ ∧
                                                  let cHaar :=
                                                    ((Measure.map
                                                      (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                                        W₂ B₂ U₀)
                                                      rawHaar).addHaarScalarFactor
                                                        (originalTupleVolume d))
                                                  let Ddet := Cdet * ε⁻¹
                                                  let Dvol :=
                                                    (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                                  let Cprior := ENNReal.ofReal Kprior * Dvol
                                                  Cprior < ∞ ∧
                                                    (∀ᵐ E ∂μprior.restrict rankCutSource,
                                                      0 < fixedResidual E) ∧
                                                      residualNegPowerIntegrableOn
                                                        (W := W₂) (B := B₂) (U₀ := U₀)
                                                        (hU₀ := hU₀)
                                                        (fun E : EdgeFamily ↦ E)
                                                        rankCutSource μprior t := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback cOneReadout sourceDensity coordinateSourceMeasure
    rawOrderOnEndpoint rawDetChart rawSourceSet p13SourceSet rawChart d
    originalVolume pivotNext signedBox sourceCylinder activeChart activeWriteback
    sourceStratum rankEq
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet, rawChart,
          d, originalVolume, pivotNext, signedBox, sourceCylinder, activeChart,
          activeWriteback, sourceStratum, rankEq] using
          exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_rankCutSource_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
            W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
            sourceImageDensity Rres G hGopen hz₀G hGdet
            (r := r) (rEdge := rEdge) hprod) with
    ⟨W, hWopen, hz₀W, hWG, V, hVopen, hz₀V, hVW, hleftV,
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV, himage_rank, hsourceCylinder_package⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
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
    ⟨W, hWopen, hz₀W, hWG, V, hVopen, hz₀V, hVW, hleftV',
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV', himage_rank, ?_⟩
  intro rawHaar hrawHaar rankCutSource μprior fixedResidual productResidual ε
    hcOne_support hsource_lower hε_ne_zero hε_ne_top Kprior hprior_upper
    hproductResidual_pos_ae
  have hrankCut_subset_V : rankCutSource ⊆ sourceChart '' V := by
    intro E hE
    rw [himageV]
    exact hE.1
  have hrankCut_subset_cylinder_V :
      rankCutSource ⊆ sourceChart '' (V ∩ sourceCylinder) := by
    simpa [Θ, EdgeFamily, sourceChart, readback, cOneReadout, signedBox,
      sourceCylinder] using
      chartPiece_subset_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_inter_sourceCylinder_of_cOneReadout_mem
        W₂ B₂ n hS hcont hnext hU₀ eNext e Rres
        hleftV' hrankCut_subset_V hcOne_support
  have hrankCut_subset_cylinder_W :
      rankCutSource ⊆ sourceChart '' (W ∩ sourceCylinder) := by
    intro E hE
    rcases hrankCut_subset_cylinder_V hE with ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hVW hz.1, hz.2⟩, rfl⟩
  simpa [rankCutSource, μprior, fixedResidual, productResidual] using
    hsourceCylinder_package rawHaar (ε := ε)
      hrankCut_subset_cylinder_W hsource_lower hε_ne_zero hε_ne_top
      (Kprior := Kprior) hprior_upper hproductResidual_pos_ae


set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Produces theta-side product-residual positivity before the active-containment bridge.
/-- Rank-cut residual source hypotheses from active endpoint-patch containment,
with theta-side product-residual positivity produced internally.

This theorem composes the coordinate-source finite-integral theorem with the
active-containment rank-cut residual-source bridge.  It first constructs an
open positivity shrink for `coordinateSourceMeasure`, then runs the active
endpoint-patch theorem inside that shrink and transfers a.e. positivity to the
smaller returned rank-cut shrink.  It still does not prove active containment,
determinant/raw Haar transport, source-prior transport, the density lower and
upper bounds, source-rank coverage, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower_priorDensity_upper_of_sourceDensity_continuousAt_lt_top_of_continuousAt_priorDensity_of_subset_detSector
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hRres : ∀ i, 0 < Rres i)
    (hsource_cont :
      ContinuousAt
        (fun z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          sourceImageDensity
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hsource_finite :
      sourceImageDensity
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < ∞)
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
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure : Measure Θ :=
      baseJ.withDensity sourceDensity
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
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume : Measure EdgeFamily :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    ∃ W : Set Θ,
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ G ∧
        ∃ V : Set Θ,
          IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
            (∀ z ∈ V, readback (sourceChart z) = z) ∧
              Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
                  IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                    sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                      MeasurableSet
                        ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                        (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                          sourceChart '' (V ∩ rankEq) =
                            (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                            ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                              let rankCutSource : Set EdgeFamily :=
                                (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
                              let μprior : Measure EdgeFamily :=
                                originalEdgeFamilyPrior
                                  (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density
                              let fixedResidual : EdgeFamily → ℝ := fun E ↦
                                aoyagiCoordinateSquareSum
                                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                                    (K := ℝ) W₂ B₂ U₀ hU₀
                                    (fun E : EdgeFamily ↦ E) E)
                              ∀ {ε : ℝ≥0∞},
                                let P : Set RawTuple :=
                                  rawSourceSet ∩ rawChart ⁻¹' rankCutSource
                                let endpointPatch : Set RawTuple :=
                                  rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P
                                let activePatchImage := activeChart '' (W ∩ sourceCylinder)
                                endpointPatch ⊆ activeWriteback '' activePatchImage →
                                  (∀ᵐ z ∂baseJ.restrict W, ε ≤ sourceDensity z) →
                                    ε ≠ 0 →
                                      ε ≠ ∞ →
                                        ∀ {Kprior : ℝ},
                                          (∀ᵐ E ∂ originalVolume.restrict rankCutSource,
                                            density E ≤ Kprior) →
                                            ∃ Cdet : ℝ≥0∞,
                                              Cdet < ∞ ∧
                                                let cHaar :=
                                                  ((Measure.map
                                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                                      W₂ B₂ U₀)
                                                    rawHaar).addHaarScalarFactor
                                                      (originalTupleVolume d))
                                                let Ddet := Cdet * ε⁻¹
                                                let Dvol :=
                                                  (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                                let Cprior := ENNReal.ofReal Kprior * Dvol
                                                Cprior < ∞ ∧
                                                  (∀ᵐ E ∂μprior.restrict rankCutSource,
                                                    0 < fixedResidual E) ∧
                                                    residualNegPowerIntegrableOn
                                                      (W := W₂) (B := B₂) (U₀ := U₀)
                                                      (hU₀ := hU₀)
                                                      (fun E : EdgeFamily ↦ E)
                                                      rankCutSource μprior t := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawOrderOnEndpoint
    rawDetChart rawSourceSet p13SourceSet rawChart d originalVolume pivotNext
    signedBox sourceCylinder activeChart activeWriteback sourceStratum rankEq
  have hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
    hGdet hz₀G
  rcases
      exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_sourceDensity_continuousAt_lt_top
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        (hDomainOpens := inferInstance)
        (hDomainBorel := inferInstance)
        (hDomainPolish := inferInstance)
        eNext e z₀ hdet₀ hpivot₀ hF₀det sourceImageDensity
        (t := t) Rres ht hRres hcrit G hGopen hz₀G
        hsource_cont hsource_finite with
    ⟨_passiveLocalSet, _passiveMeasure, _followingPatch, _K, Vpos,
      _hpassive_mem, _hpassive_open, _hpassive_meas, _hpassive_eq,
      _hpassive_lt_top, _hpassive_le, _hK_pos, _hfollowing_mem,
      _hfollowing_open, _hfollowing_meas, _hfollowing_lt_top,
      _hfollowing_det, _hfollowing_bound, hVposopen, hz₀Vpos,
      hVposG, _hVpos_passive, _hVpos_following, _hVpos_det,
      _hleftVpos, _hsource_injVpos, _hsource_contOnVpos,
      _hsource_image_measVpos, hproduct_pos_int_Vpos⟩
  have hproduct_pos_Vpos := hproduct_pos_int_Vpos.1
  have hVposdet :
      Vpos ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J := fun z hz ↦
    hGdet (hVposG hz)
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet,
          rawChart, d, originalVolume, pivotNext, signedBox, sourceCylinder,
          activeChart, activeWriteback, sourceStratum, rankEq] using
          exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
            W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
            sourceImageDensity Rres Vpos hVposopen hz₀Vpos hVposdet
            (r := r) (rEdge := rEdge) hprod) with
    ⟨W, hWopen, hz₀W, hWVpos, V, hVopen, hz₀V, hVW, hleftV,
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV, himage_rank, hpackage⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
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
    ⟨W, hWopen, hz₀W, (fun z hzW ↦ hVposG (hWVpos hzW)),
      V, hVopen, hz₀V, hVW, hleftV', hsource_injV, hsource_contOnV,
      hpiece_meas, hpiece_open, himageV, hrankPiece_meas, hiffV',
      himage_rank, ?_⟩
  intro rawHaar hrawHaar rankCutSource μprior fixedResidual ε P
    endpointPatch activePatchImage hpatch hsource_lower hε_ne_zero hε_ne_top
    Kprior hprior_upper
  let productResidual : Θ → ℝ := fun z ↦
    aoyagiCoordinateSquareSum
      (case2PassiveThetaWithFollowingFactorProductResidualReadout
        n hS hcont hnext z eNext e)
  have hV_sub_Vpos : V ⊆ Vpos := fun z hzV ↦ hWVpos (hVW hzV)
  have hrestrict_le :
      coordinateSourceMeasure.restrict V ≤ coordinateSourceMeasure.restrict Vpos :=
    Measure.restrict_mono hV_sub_Vpos le_rfl
  have hproduct_pos_Vpos' :
      ∀ᵐ z ∂ coordinateSourceMeasure.restrict Vpos,
        0 < productResidual z := by
    simpa [productResidual, coordinateSourceMeasure, sourceDensity, sourceChart,
      baseJ, referenceSource, jacobianDensity, Y,
      case2PassiveThetaWithFollowingFactorProductResidualReadout] using
      hproduct_pos_Vpos
  have hproduct_pos_V :
      ∀ᵐ z ∂ coordinateSourceMeasure.restrict V,
        0 < productResidual z :=
    (Measure.absolutelyContinuous_of_le hrestrict_le).ae_le hproduct_pos_Vpos'
  simpa [rankCutSource, μprior, fixedResidual, productResidual] using
    hpackage rawHaar (ε := ε) hpatch hsource_lower hε_ne_zero hε_ne_top
      (Kprior := Kprior) hprior_upper hproduct_pos_V

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Produces local source/prior density bounds before the active-containment bridge.
/-- Rank-cut residual source hypotheses from active endpoint-patch containment,
with theta-side product-residual positivity and local density bounds produced
internally.

The shrink depends on fixed constants `ε` and `Kprior`: continuity turns the
strict basepoint inequalities into pointwise bounds on a neighborhood, and the
returned `W` and `V` lie inside that neighborhood.  The theorem still does not
prove active containment, determinant/raw Haar transport, source-prior
transport, source-rank coverage, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_of_sourceDensity_continuousAt_lt_top_strict_sourceDensity_lower_strict_priorDensity_upper_of_continuousAt_priorDensity_of_subset_detSector
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hRres : ∀ i, 0 < Rres i)
    (hsource_cont :
      ContinuousAt
        (fun z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          sourceImageDensity
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hsource_finite :
      sourceImageDensity
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < ∞)
    {ε : ℝ≥0∞}
    (hsource_lt :
      ε <
        sourceImageDensity
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z₀))
    (hε_ne_zero : ε ≠ 0)
    {Kprior : ℝ}
    (hprior_lt :
      density
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < Kprior)
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
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure : Measure Θ :=
      baseJ.withDensity sourceDensity
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
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let d := paperEndpointFixedBaseDim W₂ B₂ U₀
    let originalVolume : Measure EdgeFamily :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let signedBox := SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres
    let sourceCylinder : Set Θ := {z | z.1.yNext ∈ signedBox}
    let activeChart : Θ → Θ :=
      fun z ↦
        ((z.1.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    let activeWriteback : Θ ≃L[ℝ] RawTuple :=
      (Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveContinuousLinearEquiv
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n e).symm
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    ∃ W : Set Θ,
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ G ∧
        ∃ V : Set Θ,
          IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
            (∀ z ∈ V, readback (sourceChart z) = z) ∧
              Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
                  IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                    sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                      MeasurableSet
                        ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                        (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                          sourceChart '' (V ∩ rankEq) =
                            (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                            ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                              let rankCutSource : Set EdgeFamily :=
                                (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
                              let μprior : Measure EdgeFamily :=
                                originalEdgeFamilyPrior
                                  (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density
                              let fixedResidual : EdgeFamily → ℝ := fun E ↦
                                aoyagiCoordinateSquareSum
                                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                                    (K := ℝ) W₂ B₂ U₀ hU₀
                                    (fun E : EdgeFamily ↦ E) E)
                              let P : Set RawTuple :=
                                rawSourceSet ∩ rawChart ⁻¹' rankCutSource
                              let endpointPatch : Set RawTuple :=
                                rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P
                              let activePatchImage := activeChart '' (W ∩ sourceCylinder)
                              endpointPatch ⊆ activeWriteback '' activePatchImage →
                                ∃ Cdet : ℝ≥0∞,
                                  Cdet < ∞ ∧
                                    let cHaar :=
                                      ((Measure.map
                                        (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                          W₂ B₂ U₀)
                                        rawHaar).addHaarScalarFactor
                                          (originalTupleVolume d))
                                    let Ddet := Cdet * ε⁻¹
                                    let Dvol :=
                                      (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                    let Cprior := ENNReal.ofReal Kprior * Dvol
                                    Cprior < ∞ ∧
                                      (∀ᵐ E ∂μprior.restrict rankCutSource,
                                        0 < fixedResidual E) ∧
                                        residualNegPowerIntegrableOn
                                          (W := W₂) (B := B₂) (U₀ := U₀)
                                          (hU₀ := hU₀)
                                          (fun E : EdgeFamily ↦ E)
                                          rankCutSource μprior t := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawOrderOnEndpoint
    rawDetChart rawSourceSet p13SourceSet rawChart d originalVolume pivotNext
    signedBox sourceCylinder activeChart activeWriteback sourceStratum rankEq
  have hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
    hGdet hz₀G
  have hsourceChart_cont : ContinuousAt sourceChart z₀ := by
    simpa [Θ, EdgeFamily, sourceChart] using
      continuousAt_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_detSector_pivotNonzero
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀
  have hprior_pullback :
      ContinuousAt (fun z : Θ ↦ density (sourceChart z)) z₀ := by
    exact
      ContinuousAt.comp
        (x := z₀) (f := sourceChart) (g := density)
        (by simpa [sourceChart] using hprior_cont) hsourceChart_cont
  have hbounds_eventually :
      (∀ᶠ z in nhds z₀, ε ≤ sourceImageDensity (sourceChart z)) ∧
        (∀ᶠ z in nhds z₀, density (sourceChart z) ≤ Kprior) :=
    eventually_sourceImageDensity_comp_lower_priorDensity_comp_upper_of_continuousAt
      (sourceChart := sourceChart) (sourceImageDensity := sourceImageDensity)
      (density := density) (z₀ := z₀) (ε := ε) (Kprior := Kprior)
      (by simpa [sourceChart] using hsource_cont)
      (by simpa [sourceChart] using hsource_lt)
      hprior_pullback
      (by simpa [sourceChart] using hprior_lt)
  rcases
      eventually_nhds_iff.mp (hbounds_eventually.1.and hbounds_eventually.2) with
    ⟨Gbounds, hGbounds, hGbounds_open, hz₀Gbounds⟩
  let Gshrink : Set Θ := G ∩ Gbounds
  have hGshrink_open : IsOpen Gshrink := hGopen.inter hGbounds_open
  have hz₀Gshrink : z₀ ∈ Gshrink := ⟨hz₀G, hz₀Gbounds⟩
  have hGshrink_det :
      Gshrink ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J := fun z hz ↦
    hGdet hz.1
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawOrderOnEndpoint, rawDetChart, rawSourceSet, p13SourceSet,
          rawChart, d, originalVolume, pivotNext, signedBox, sourceCylinder,
          activeChart, activeWriteback, sourceStratum, rankEq] using
          exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower_priorDensity_upper_of_sourceDensity_continuousAt_lt_top_of_continuousAt_priorDensity_of_subset_detSector
            W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
            sourceImageDensity Rres hRres hsource_cont hsource_finite
            Gshrink hGshrink_open hz₀Gshrink hGshrink_det
            (r := r) (rEdge := rEdge) hprod) with
    ⟨W, hWopen, hz₀W, hWGshrink, V, hVopen, hz₀V, hVW, hleftV,
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV, himage_rank, hpackage⟩
  have hWG : W ⊆ G := fun z hzW ↦ (hWGshrink hzW).1
  have hWbounds : W ⊆ Gbounds := fun z hzW ↦ (hWGshrink hzW).2
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
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
    ⟨W, hWopen, hz₀W, hWG, V, hVopen, hz₀V, hVW, hleftV',
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV', himage_rank, ?_⟩
  intro rawHaar hrawHaar rankCutSource μprior fixedResidual P endpointPatch
    activePatchImage hpatch
  have hsource_lower :
      ∀ᵐ z ∂baseJ.restrict W, ε ≤ sourceDensity z := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with z hzW
    exact (hGbounds z (hWbounds hzW)).1
  have hrankCut_subset_V : rankCutSource ⊆ sourceChart '' V := by
    intro E hE
    rw [himageV]
    exact hE.1
  have hprior_point :
      ∀ E ∈ rankCutSource, density E ≤ Kprior := by
    intro E hE
    rcases hrankCut_subset_V hE with ⟨z, hzV, rfl⟩
    exact (hGbounds z (hWbounds (hVW hzV))).2
  have hprior_upper :
      ∀ᵐ E ∂ originalVolume.restrict rankCutSource,
        density E ≤ Kprior :=
    ae_restrict_upper_of_forall_mem hrankPiece_meas hprior_point
  have hε_ne_top : ε ≠ ∞ :=
    ne_top_of_lt (lt_trans hsource_lt hsource_finite)
  simpa [rankCutSource, μprior, fixedResidual] using
    hpackage rawHaar (ε := ε) hpatch hsource_lower hε_ne_zero hε_ne_top
      (Kprior := Kprior) hprior_upper

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Produces the theta-side product-residual positivity before applying the endpoint-prior bridge.
/-- Rank-cut residual source hypotheses from endpoint-reference prior readback
domination, with theta-side product-residual positivity produced internally.

This theorem composes the coordinate-source finite-integral theorem with the
endpoint-prior rank-cut residual-source bridge.  It first constructs an open
positivity shrink for `coordinateSourceMeasure`, then runs the existing
endpoint-prior theorem inside that shrink and transfers a.e. positivity to the
smaller returned rank-cut shrink by absolute continuity of restricted
measures.  It still does not prove endpoint-reference Haar transport,
determinant/raw Haar transport, source-prior transport, the density lower and
upper bounds, source-rank coverage, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper_of_sourceDensity_continuousAt_lt_top_of_continuousAt_priorDensity_of_subset_detSector
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hRres : ∀ i, 0 < Rres i)
    (hsource_cont :
      ContinuousAt
        (fun z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          sourceImageDensity
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hsource_finite :
      sourceImageDensity
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < ∞)
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
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure : Measure Θ :=
      baseJ.withDensity sourceDensity
    let rawMap : Θ → RawTuple :=
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
    let endpointJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
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
    let originalVolume : Measure EdgeFamily :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    ∃ W : Set Θ,
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ G ∧
        ∃ V : Set Θ,
          IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
            (∀ z ∈ V, readback (sourceChart z) = z) ∧
              Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
                  IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                    sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                      MeasurableSet
                        ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                        (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                          sourceChart '' (V ∩ rankEq) =
                            (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                            ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                              let rankCutSource : Set EdgeFamily :=
                                (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
                              let μprior : Measure EdgeFamily :=
                                originalEdgeFamilyPrior
                                  (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density
                              let fixedResidual : EdgeFamily → ℝ := fun E ↦
                                aoyagiCoordinateSquareSum
                                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                                    (K := ℝ) W₂ B₂ U₀ hU₀
                                    (fun E : EdgeFamily ↦ E) E)
                              ∀ {Cdet ε : ℝ≥0∞},
                                let P : Set RawTuple :=
                                  rawSourceSet ∩ rawChart ⁻¹' rankCutSource
                                let endpointReferenceImage : Measure RawTuple :=
                                  case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                                    (κ' := throughSubspaceEndpointComplementIndex
                                      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                                    n hS hcont hnext eNext e Rres W
                                endpointReferenceImage =
                                    (rawHaar.restrict
                                      (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P)).withDensity
                                      endpointJacobianDensity →
                                  Cdet < ∞ →
                                    (∀ᵐ y ∂rawHaar.restrict
                                        (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P),
                                      1 ≤ Cdet * endpointJacobianDensity y) →
                                      (∀ᵐ z ∂baseJ.restrict W, ε ≤ sourceDensity z) →
                                        ε ≠ 0 →
                                          ε ≠ ∞ →
                                            ∀ {Kprior : ℝ},
                                              (∀ᵐ E ∂ originalVolume.restrict rankCutSource,
                                                density E ≤ Kprior) →
                                                let cHaar :=
                                                  ((Measure.map
                                                    (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                                      W₂ B₂ U₀)
                                                    rawHaar).addHaarScalarFactor
                                                      (originalTupleVolume d))
                                                let Ddet := Cdet * ε⁻¹
                                                let Dvol :=
                                                  (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                                let Cprior := ENNReal.ofReal Kprior * Dvol
                                                Cprior < ∞ ∧
                                                  (∀ᵐ E ∂μprior.restrict rankCutSource,
                                                    0 < fixedResidual E) ∧
                                                    residualNegPowerIntegrableOn
                                                      (W := W₂) (B := B₂) (U₀ := U₀)
                                                      (hU₀ := hU₀)
                                                      (fun E : EdgeFamily ↦ E)
                                                      rankCutSource μprior t := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart endpointJacobianDensity rawSourceSet
    p13SourceSet rawChart d originalVolume sourceStratum rankEq
  have hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
    hGdet hz₀G
  rcases
      exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_sourceDensity_continuousAt_lt_top
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        (hDomainOpens := inferInstance)
        (hDomainBorel := inferInstance)
        (hDomainPolish := inferInstance)
        eNext e z₀ hdet₀ hpivot₀ hF₀det sourceImageDensity
        (t := t) Rres ht hRres hcrit G hGopen hz₀G
        hsource_cont hsource_finite with
    ⟨_passiveLocalSet, _passiveMeasure, _followingPatch, _K, Vpos,
      _hpassive_mem, _hpassive_open, _hpassive_meas, _hpassive_eq,
      _hpassive_lt_top, _hpassive_le, _hK_pos, _hfollowing_mem,
      _hfollowing_open, _hfollowing_meas, _hfollowing_lt_top,
      _hfollowing_det, _hfollowing_bound, hVposopen, hz₀Vpos,
      hVposG, _hVpos_passive, _hVpos_following, _hVpos_det,
      _hleftVpos, _hsource_injVpos, _hsource_contOnVpos,
      _hsource_image_measVpos, hproduct_pos_int_Vpos⟩
  have hproduct_pos_Vpos := hproduct_pos_int_Vpos.1
  have hVposdet :
      Vpos ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J := fun z hz ↦
    hGdet (hVposG hz)
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawMap, rawOrderOnEndpoint, rawDetChart, endpointJacobianDensity,
          rawSourceSet, p13SourceSet, rawChart, d, originalVolume,
          sourceStratum, rankEq] using
          exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
            W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
            sourceImageDensity Rres Vpos hVposopen hz₀Vpos hVposdet
            (r := r) (rEdge := rEdge) hprod) with
    ⟨W, hWopen, hz₀W, hWVpos, V, hVopen, hz₀V, hVW, hleftV,
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV, himage_rank, hpackage⟩
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
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
    ⟨W, hWopen, hz₀W, (fun z hzW ↦ hVposG (hWVpos hzW)),
      V, hVopen, hz₀V, hVW, hleftV', hsource_injV, hsource_contOnV,
      hpiece_meas, hpiece_open, himageV, hrankPiece_meas, hiffV',
      himage_rank, ?_⟩
  intro rawHaar hrawHaar rankCutSource μprior fixedResidual Cdet ε P
    endpointReferenceImage hendpoint hCdet hendpoint_lower hsource_lower
    hε_ne_zero hε_ne_top Kprior hprior_upper cHaar Ddet Dvol Cprior
  let productResidual : Θ → ℝ := fun z ↦
    aoyagiCoordinateSquareSum
      (case2PassiveThetaWithFollowingFactorProductResidualReadout
        n hS hcont hnext z eNext e)
  have hV_sub_Vpos : V ⊆ Vpos := fun z hzV ↦ hWVpos (hVW hzV)
  have hrestrict_le :
      coordinateSourceMeasure.restrict V ≤ coordinateSourceMeasure.restrict Vpos :=
    Measure.restrict_mono hV_sub_Vpos le_rfl
  have hproduct_pos_Vpos' :
      ∀ᵐ z ∂ coordinateSourceMeasure.restrict Vpos,
        0 < productResidual z := by
    simpa [productResidual, coordinateSourceMeasure, sourceDensity, sourceChart,
      baseJ, referenceSource, jacobianDensity, Y,
      case2PassiveThetaWithFollowingFactorProductResidualReadout] using
      hproduct_pos_Vpos
  have hproduct_pos_V :
      ∀ᵐ z ∂ coordinateSourceMeasure.restrict V,
        0 < productResidual z :=
    (Measure.absolutelyContinuous_of_le hrestrict_le).ae_le hproduct_pos_Vpos'
  simpa [rankCutSource, μprior, fixedResidual, productResidual, cHaar, Ddet,
    Dvol, Cprior] using
    hpackage rawHaar (Cdet := Cdet) (ε := ε)
      hendpoint hCdet hendpoint_lower hsource_lower hε_ne_zero hε_ne_top
      (Kprior := Kprior) hprior_upper hproduct_pos_V

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- Produces local source/prior density bounds before applying the endpoint-prior bridge.
/-- Rank-cut residual source hypotheses from endpoint-reference prior readback
domination, with theta-side product-residual positivity and local density
bounds produced internally.

The shrink now depends on fixed constants `ε` and `Kprior`: continuity turns
the strict basepoint inequalities into pointwise bounds on a neighborhood, and
the returned `W` and `V` lie inside that neighborhood.  The theorem still does
not prove endpoint-reference Haar transport, determinant/raw Haar transport,
source-prior transport, source-rank coverage, normal crossings, pole order, or
RLCT extraction. -/
theorem exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_of_sourceDensity_continuousAt_lt_top_strict_sourceDensity_lower_strict_priorDensity_upper_of_continuousAt_priorDensity_of_subset_detSector
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
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hRres : ∀ i, 0 < Rres i)
    (hsource_cont :
      ContinuousAt
        (fun z :
          Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
          sourceImageDensity
            (case2PassiveThetaWithFollowingFactorEndpointSourceChart
              W₂ B₂ n hS hcont hnext hU₀ eNext e z)) z₀)
    (hsource_finite :
      sourceImageDensity
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < ∞)
    {ε : ℝ≥0∞}
    (hsource_lt :
      ε <
        sourceImageDensity
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z₀))
    (hε_ne_zero : ε ≠ 0)
    {Kprior : ℝ}
    (hprior_lt :
      density
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z₀) < Kprior)
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
    let Y : Θ → RawTuple :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let referenceSource : Measure Θ :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext Rres
    let jacobianDensity : Θ → ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ : Measure Θ := referenceSource.withDensity jacobianDensity
    let sourceChart : Θ → EdgeFamily :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let sourceDensity : Θ → ℝ≥0∞ :=
      fun z ↦ sourceImageDensity (sourceChart z)
    let coordinateSourceMeasure : Measure Θ :=
      baseJ.withDensity sourceDensity
    let rawMap : Θ → RawTuple :=
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
    let endpointJacobianDensity : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y)
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
    let originalVolume : Measure EdgeFamily :=
      originalEdgeFamilyVolume (V := reverseVertex W₂)
        (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
    let sourceStratum : Set EdgeFamily :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    let rankEq : Set Θ :=
      {z |
        r + z.2.rank = rEdge 0 ∧
          r + (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).rank =
            rEdge 1}
    ∃ W : Set Θ,
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ G ∧
        ∃ V : Set Θ,
          IsOpen V ∧ z₀ ∈ V ∧ V ⊆ W ∧
            (∀ z ∈ V, readback (sourceChart z) = z) ∧
              Set.InjOn sourceChart V ∧ ContinuousOn sourceChart V ∧
                MeasurableSet (p13SourceSet ∩ readback ⁻¹' V) ∧
                  IsOpen (p13SourceSet ∩ readback ⁻¹' V) ∧
                    sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
                      MeasurableSet
                        ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ∧
                        (∀ z ∈ V, sourceChart z ∈ sourceStratum ↔ z ∈ rankEq) ∧
                          sourceChart '' (V ∩ rankEq) =
                            (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum ∧
                            ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
                              let rankCutSource : Set EdgeFamily :=
                                (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum
                              let μprior : Measure EdgeFamily :=
                                originalEdgeFamilyPrior
                                  (V := reverseVertex W₂)
                                  (paperEndpointFixedBaseFinBasis W₂ B₂ U₀ hU₀)
                                  density
                              let fixedResidual : EdgeFamily → ℝ := fun E ↦
                                aoyagiCoordinateSquareSum
                                  (paperEndpointFixedBaseResidualBlockCoordinateMap
                                    (K := ℝ) W₂ B₂ U₀ hU₀
                                    (fun E : EdgeFamily ↦ E) E)
                              ∀ {Cdet : ℝ≥0∞},
                                let P : Set RawTuple :=
                                  rawSourceSet ∩ rawChart ⁻¹' rankCutSource
                                let endpointReferenceImage : Measure RawTuple :=
                                  case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
                                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ)
                                    (κ' := throughSubspaceEndpointComplementIndex
                                      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
                                    n hS hcont hnext eNext e Rres W
                                endpointReferenceImage =
                                    (rawHaar.restrict
                                      (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P)).withDensity
                                      endpointJacobianDensity →
                                  Cdet < ∞ →
                                    (∀ᵐ y ∂rawHaar.restrict
                                        (rawDetChart ∩ rawOrderOnEndpoint ⁻¹' P),
                                      1 ≤ Cdet * endpointJacobianDensity y) →
                                      let cHaar :=
                                        ((Measure.map
                                          (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
                                            W₂ B₂ U₀)
                                          rawHaar).addHaarScalarFactor
                                            (originalTupleVolume d))
                                      let Ddet := Cdet * ε⁻¹
                                      let Dvol :=
                                        (((cHaar⁻¹ : NNReal) : ℝ≥0∞) * Ddet)
                                      let Cprior := ENNReal.ofReal Kprior * Dvol
                                      Cprior < ∞ ∧
                                        (∀ᵐ E ∂μprior.restrict rankCutSource,
                                          0 < fixedResidual E) ∧
                                          residualNegPowerIntegrableOn
                                            (W := W₂) (B := B₂) (U₀ := U₀)
                                            (hU₀ := hU₀)
                                            (fun E : EdgeFamily ↦ E)
                                            rankCutSource μprior t := by
  intro Θ RawTuple EdgeFamily Y referenceSource jacobianDensity baseJ
    sourceChart readback sourceDensity coordinateSourceMeasure rawMap
    rawOrderOnEndpoint rawDetChart endpointJacobianDensity rawSourceSet
    p13SourceSet rawChart d originalVolume sourceStratum rankEq
  have hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
    hGdet hz₀G
  have hsourceChart_cont : ContinuousAt sourceChart z₀ := by
    simpa [Θ, EdgeFamily, sourceChart] using
      continuousAt_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_detSector_pivotNonzero
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀)
        eNext e z₀ hdet₀ hpivot₀
  have hprior_pullback :
      ContinuousAt (fun z : Θ ↦ density (sourceChart z)) z₀ := by
    exact
      ContinuousAt.comp
        (x := z₀) (f := sourceChart) (g := density)
        (by simpa [sourceChart] using hprior_cont) hsourceChart_cont
  have hbounds_eventually :
      (∀ᶠ z in nhds z₀, ε ≤ sourceImageDensity (sourceChart z)) ∧
        (∀ᶠ z in nhds z₀, density (sourceChart z) ≤ Kprior) :=
    eventually_sourceImageDensity_comp_lower_priorDensity_comp_upper_of_continuousAt
      (sourceChart := sourceChart) (sourceImageDensity := sourceImageDensity)
      (density := density) (z₀ := z₀) (ε := ε) (Kprior := Kprior)
      (by simpa [sourceChart] using hsource_cont)
      (by simpa [sourceChart] using hsource_lt)
      hprior_pullback
      (by simpa [sourceChart] using hprior_lt)
  rcases
      eventually_nhds_iff.mp (hbounds_eventually.1.and hbounds_eventually.2) with
    ⟨Gbounds, hGbounds, hGbounds_open, hz₀Gbounds⟩
  let Gshrink : Set Θ := G ∩ Gbounds
  have hGshrink_open : IsOpen Gshrink := hGopen.inter hGbounds_open
  have hz₀Gshrink : z₀ ∈ Gshrink := ⟨hz₀G, hz₀Gbounds⟩
  have hGshrink_det :
      Gshrink ⊆
        case2PassiveThetaWithFollowingFactorDetSector
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J := fun z hz ↦
    hGdet hz.1
  rcases
      (by
        simpa [Θ, RawTuple, EdgeFamily, Y, referenceSource, jacobianDensity,
          baseJ, sourceChart, readback, sourceDensity, coordinateSourceMeasure,
          rawMap, rawOrderOnEndpoint, rawDetChart, endpointJacobianDensity,
          rawSourceSet, p13SourceSet, rawChart, d, originalVolume,
          sourceStratum, rankEq] using
          exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper_of_sourceDensity_continuousAt_lt_top_of_continuousAt_priorDensity_of_subset_detSector
            W₂ B₂ n (S := S) (J := J) hS hcont hnext
            (U₀ := U₀) (hU₀ := hU₀) eNext e z₀ hpivot₀ hF₀det
            (t := t) ht hcrit (density := density) hprior_cont
            sourceImageDensity Rres hRres hsource_cont hsource_finite
            Gshrink hGshrink_open hz₀Gshrink hGshrink_det
            (r := r) (rEdge := rEdge) hprod) with
    ⟨W, hWopen, hz₀W, hWGshrink, V, hVopen, hz₀V, hVW, hleftV,
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV, himage_rank, hpackage⟩
  have hWG : W ⊆ G := fun z hzW ↦ (hWGshrink hzW).1
  have hWbounds : W ⊆ Gbounds := fun z hzW ↦ (hWGshrink hzW).2
  have hleftV' : ∀ z ∈ V, readback (sourceChart z) = z := by
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
      hleftV z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
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
    ⟨W, hWopen, hz₀W, hWG, V, hVopen, hz₀V, hVW, hleftV',
      hsource_injV, hsource_contOnV, hpiece_meas, hpiece_open,
      himageV, hrankPiece_meas, hiffV', himage_rank, ?_⟩
  intro rawHaar hrawHaar rankCutSource μprior fixedResidual Cdet P
    endpointReferenceImage hendpoint hCdet hendpoint_lower cHaar Ddet Dvol Cprior
  have hsource_lower :
      ∀ᵐ z ∂baseJ.restrict W, ε ≤ sourceDensity z := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with z hzW
    exact (hGbounds z (hWbounds hzW)).1
  have hrankCut_subset_V : rankCutSource ⊆ sourceChart '' V := by
    intro E hE
    rw [himageV]
    exact hE.1
  have hprior_point :
      ∀ E ∈ rankCutSource, density E ≤ Kprior := by
    intro E hE
    rcases hrankCut_subset_V hE with ⟨z, hzV, rfl⟩
    exact (hGbounds z (hWbounds (hVW hzV))).2
  have hprior_upper :
      ∀ᵐ E ∂ originalVolume.restrict rankCutSource,
        density E ≤ Kprior :=
    ae_restrict_upper_of_forall_mem hrankPiece_meas hprior_point
  have hε_ne_top : ε ≠ ∞ :=
    ne_top_of_lt (lt_trans hsource_lt hsource_finite)
  simpa [rankCutSource, μprior, fixedResidual, cHaar, Ddet, Dvol, Cprior] using
    hpackage rawHaar (Cdet := Cdet) (ε := ε)
      hendpoint hCdet hendpoint_lower hsource_lower hε_ne_zero hε_ne_top
      (Kprior := Kprior) hprior_upper

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
