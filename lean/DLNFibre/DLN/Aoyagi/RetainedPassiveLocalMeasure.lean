import DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource

/-!
# Retained-passive local source for the p.13 local-measure handoff

This file specializes the existing local-source finite-integral consumer to
the retained-passive determinant-chart source.  It plugs in only the local
coverage and measurability theorems from `RetainedPassiveLocalSource`; residual
positivity/integrability and local loss/density bounds remain explicit
hypotheses.  It does not construct a source measure pushforward, Jacobian
density, normal-crossing chart, pole order, or RLCT extraction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

section RetainedPassiveLocalMeasure

universe v

variable {M : ℕ}
  (W : Fin (M + 2) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  (B : ∀ i : Fin (M + 1), W i.succ →ₗ[ℝ] W i.castSucc)

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- Retained-passive specialization of the source-stratum/local-source
finite-integral handoff.

The retained-passive local source supplies the local coverage and measurable
source hypotheses.  The residual positivity/integrability, local loss lower
bound, and local density bounds are still supplied on that local source. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin (M + 1),
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 1) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α} [SFinite μ]
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hCedge : Continuous Cedge)
    (hbase :
      Cedge x₀ =
        fun p : Fin (M + 1) ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hpos_local :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
    (hbase_local :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge
        (paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge) μ t)
    (hloss :
      ∀ᶠ x in nhdsWithin x₀
          (paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in nhdsWithin x₀
          (paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in nhdsWithin x₀
          (paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ ρ,
        ENNReal.ofReal
          ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount (M + 1) H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let localSource :=
    paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  rcases exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
      W B U₀ hU₀ Cedge r rEdge hCedge.continuousAt hbase with
    ⟨Ulocal, hUlocal_open, hx₀Ulocal, _hUlocal_sub, hcoverage⟩
  have hlocal_meas : MeasurableSet localSource := by
    dsimp [localSource]
    exact
      measurableSet_paperEndpointFixedBaseRetainedPassiveP13LocalSource_of_continuous
        W B U₀ hU₀ Cedge hCedge
  simpa [ρ, localSource, sourceStratum] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource
      (W := W) (B := B) sourceData
      (localSource := localSource) (μ := μ) (ν := ν)
      (loss := loss) (density := density) (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht Ulocal hUlocal_open hx₀Ulocal
      (by simpa [localSource, sourceStratum] using hcoverage)
      hlocal_meas
      (by simpa [localSource] using hpos_local)
      (by simpa [localSource, residualNegPowerIntegrableOn] using hbase_local)
      (by simpa [ρ, localSource] using hloss)
      (by simpa [ρ, localSource] using hdensity_nonneg)
      (by simpa [ρ, localSource] using hdensity_le)

end PaperEndpointFixedBaseRegularCoordinateSourceData

end RetainedPassiveLocalMeasure

end Aoyagi
end DLN
end DLNFibre
