import DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure

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

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
