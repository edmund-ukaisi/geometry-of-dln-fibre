import DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
import DLNFibre.DLN.Aoyagi.EndpointLossComparison

/-!
# Case 2 with-following product-residual bridge

This file contains the reusable residual-base handoff from the with-following
Case 2 readback product-residual integrand to the fixed-base p.13 residual
power predicate consumed by the local loss machinery.  It does not prove the
pointwise residual square-sum equality, residual positivity, source coverage,
Haar transport, normal crossings, pole order, or RLCT extraction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A finite readback product-residual integral gives the fixed-base p.13
`residualNegPowerIntegrableOn` predicate, provided the raw fixed-base residual
square-sum agrees pointwise with the readback product-residual square-sum on
the same source set.

This is only the residual-base handoff for later loss wrappers.  Positivity of
the raw residual square-sum, density bounds, adapted-product lower bounds, and
any original `lossDLN` comparison remain separate hypotheses downstream. -/
theorem residualNegPowerIntegrableOn_of_lintegral_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidual_eq
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    {source : Set
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)}
    {μ : Measure
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)}
    {t : ℝ}
    (hsource_meas : MeasurableSet source)
    (hfinite_readback :
      (∫⁻ E :
          (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ),
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t)) ∂
          μ.restrict source) < ∞)
    (hsq :
      ∀ E ∈ source,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀
            (fun E :
              (∀ p : Fin 2,
                reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
            E) =
          aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) :
    residualNegPowerIntegrableOn
      (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
      (fun E :
        (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
      source μ t := by
  have hcongr :
      (fun E :
          (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀
              (fun E :
                (∀ p : Fin 2,
                  reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
              E)) ^ (-t))) =ᵐ[μ.restrict source]
      (fun E :
          (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
              W₂ B₂ n hS hcont hnext hU₀ eNext e E)) ^ (-t))) := by
    filter_upwards [ae_restrict_mem hsource_meas] with E hE
    exact congrArg (fun q : ℝ ↦ ENNReal.ofReal (q ^ (-t))) (hsq E hE)
  change
    (∫⁻ E :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ),
      ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀
            (fun E :
              (∀ p : Fin 2,
                reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
            E)) ^ (-t)) ∂ μ.restrict source) < ∞
  rw [lintegral_congr_ae hcongr]
  exact hfinite_readback

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- On a local with-following p.13/readback rank-cut patch, the original
fixed-basis square-Frobenius loss dominates the readback product-residual
square-sum up to a positive scalar.

This is a function comparison.  The local image, left-inverse, determinant
sector, and source-rank hypotheses remain explicit; no source/prior measure
transport, integrability, normal-crossing, pole-order, or RLCT statement is
claimed. -/
theorem exists_pos_const_eventually_readbackProductResidual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_rankCut_of_sourceChart_image_eq
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
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :
    let Θ :=
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart : Θ → EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let readback : EdgeFamily → Θ :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∀ {V : Set Θ},
      (∀ z ∈ V, readback (sourceChart z) = z) →
        sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V →
          V ⊆ case2PassiveThetaWithFollowingFactorDetSector
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
            ∀ {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ},
              let sourceStratum : Set EdgeFamily :=
                paperEndpointFixedBaseSourceRankStratum
                  (K := ℝ) (N := 2) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
              PaperEndpointFixedBaseRegularCoordinateSourceData
                (K := ℝ) W₂ B₂ U₀ hU₀ (sourceChart z₀)
                (fun E : EdgeFamily ↦ E) H r rEdge →
                sourceChart z₀ =
                  (fun p : Fin 2 ↦
                    LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) →
                  ∀ {d : Fin 3 → ℕ},
                    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W₂ j)) →
                      ∃ c : ℝ, 0 < c ∧
                        ∀ᶠ E in nhdsWithin (sourceChart z₀)
                            ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
                          c *
                              aoyagiCoordinateSquareSum
                                (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
                                  W₂ B₂ n hS hcont hnext hU₀ eNext e E) ≤
                            lossDLN d
                              (LinearMap.toMatrix (b 0) (b (Fin.last 2))
                                (chainMap (reverseVertex W₂) (reverseEdge W₂ B₂)
                                  0 (Fin.last 2) (Fin.zero_le (Fin.last 2))))
                              (chainMapMatrixTuple b
                                (fun p : Fin 2 ↦
                                  (E p :
                                    reverseVertex W₂ p.castSucc →ₗ[ℝ]
                                      reverseVertex W₂ p.succ))) := by
  intro Θ EdgeFamily sourceChart readback p13SourceSet V hleft himage hVdet
    H r rEdge sourceStratum sourceData hbase d b
  rcases
      exists_pos_const_half_regular_add_residual_squareSum_eventually_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_source
        (W := W₂) (B := B₂) (d := d) b
        (x₀ := sourceChart z₀)
        (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := fun E : EdgeFamily ↦ E)
        sourceData
        (show ContinuousAt (fun E : EdgeFamily ↦ E) (sourceChart z₀) from
          continuousAt_id)
        hbase with
    ⟨c₀, hc₀_pos, hloss⟩
  refine ⟨c₀ / 2, half_pos hc₀_pos, ?_⟩
  have hrank_subset_source :
      ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum) ⊆ sourceStratum := by
    intro E hE
    exact hE.2
  have hloss_rank :
      ∀ᶠ E in nhdsWithin (sourceChart z₀)
          ((p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum),
        (c₀ / 2) *
            (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseRegularBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E) +
              aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ≤
          lossDLN d
            (LinearMap.toMatrix (b 0) (b (Fin.last 2))
              (chainMap (reverseVertex W₂) (reverseEdge W₂ B₂)
                0 (Fin.last 2) (Fin.zero_le (Fin.last 2))))
            (chainMapMatrixTuple b
              (fun p : Fin 2 ↦
                (E p :
                  reverseVertex W₂ p.castSucc →ₗ[ℝ]
                    reverseVertex W₂ p.succ))) :=
    hloss.filter_mono (nhdsWithin_mono _ hrank_subset_source)
  filter_upwards [hloss_rank, eventually_mem_nhdsWithin] with E hle hE
  have hE_image : E ∈ sourceChart '' V := by
    rw [himage]
    exact hE.1
  rcases hE_image with ⟨z, hzV, rfl⟩
  have hdet_z :
      (case2PassiveThetaWithFollowingFactorEndpointRetainedData
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e).detChart :=
    case2PassiveThetaWithFollowingFactorEndpointRetainedData_detChart
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
      (hVdet hzV)
  have hfixed_sq :
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart z)) =
        aoyagiCoordinateSquareSum
          (case2PassiveThetaWithFollowingFactorProductResidualReadout
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e) := by
    simpa [sourceChart] using
      aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_case2PassiveThetaWithFollowingFactorEndpointSourceChart_eq_of_detChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e z hdet_z
  have hreadback_sq :
      aoyagiCoordinateSquareSum
          (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
            W₂ B₂ n hS hcont hnext hU₀ eNext e (sourceChart z)) =
        aoyagiCoordinateSquareSum
          (case2PassiveThetaWithFollowingFactorProductResidualReadout
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e) := by
    simpa [sourceChart, readback] using
      aoyagiCoordinateSquareSum_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout_sourceChart_eq_of_leftInverse
        W₂ B₂ n hS hcont hnext hU₀ eNext e z (hleft z hzV)
  have hreadback_eq_fixed :
      aoyagiCoordinateSquareSum
          (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
            W₂ B₂ n hS hcont hnext hU₀ eNext e (sourceChart z)) =
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart z)) :=
    hreadback_sq.trans hfixed_sq.symm
  have hregular_nonneg :
      0 ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseRegularBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart z)) :=
    aoyagiCoordinateSquareSum_nonneg _
  have hscalar_nonneg : 0 ≤ c₀ / 2 := le_of_lt (half_pos hc₀_pos)
  have hresidual_le_sum :
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart z)) ≤
        aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
              (sourceChart z)) +
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
              (sourceChart z)) := by
    linarith
  have hscaled :
      (c₀ / 2) *
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
              (sourceChart z)) ≤
        (c₀ / 2) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
                (sourceChart z)) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
                (sourceChart z))) :=
    mul_le_mul_of_nonneg_left hresidual_le_sum hscalar_nonneg
  calc
    (c₀ / 2) *
        aoyagiCoordinateSquareSum
          (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
            W₂ B₂ n hS hcont hnext hU₀ eNext e (sourceChart z)) =
        (c₀ / 2) *
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
              (sourceChart z)) := by
          rw [hreadback_eq_fixed]
    _ ≤
        (c₀ / 2) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
                (sourceChart z)) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
                (sourceChart z))) := hscaled
    _ ≤
        lossDLN d
          (LinearMap.toMatrix (b 0) (b (Fin.last 2))
            (chainMap (reverseVertex W₂) (reverseEdge W₂ B₂)
              0 (Fin.last 2) (Fin.zero_le (Fin.last 2))))
          (chainMapMatrixTuple b
            (fun p : Fin 2 ↦
              ((sourceChart z) p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ]
                  reverseVertex W₂ p.succ))) := hle

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
