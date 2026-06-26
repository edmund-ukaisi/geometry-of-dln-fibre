import DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource
import DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure

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

set_option linter.unusedSectionVars false in
/-- Retained-passive local-measure handoff with residual hypotheses supplied by
a weighted signed-box chart.

This specializes the retained-passive local-source handoff further: global
continuity supplies fixed-base edge-matrix measurability, and the signed-box
pushforward plus monomial residual lower bound supplies residual positivity
and negative-power integrability on the retained-passive local source.  The
pushforward, monomial data, and local loss/density bounds remain hypotheses. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialLower
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
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
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hCedge : Continuous Cedge)
    (hbase :
      Cedge x₀ =
        fun p : Fin (M + 1) ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict
          (paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
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
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            creg * (aoyagiCoordinateSquareSum
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
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
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
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            density (x, u) ≤ Creg) :
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
          ((Metric.ball (0 : EuclideanSpace ℝ ρ) Rreg).indicator
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
  have hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin (M + 1) ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))) := by
    exact
      (continuous_paperEndpointFixedBaseRetainedPassiveP13EdgeMatrix_of_continuous
        W B U₀ hU₀ Cedge hCedge).measurable
  rcases
      residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (source := localSource) (μ := μ)
        (chart := sourceChart) (density := sourceDensity)
        (t := t) (c := cres) (C := Cres) (R := Rres) (h := hres) (k := kres)
        hEdgeMatrix hsourceDensity_aemeas hsourceChart
        (by simpa [localSource] using hmap)
        hcres hCres (le_of_lt ht) hRres hcrit hres_lower
        hsourceDensity_nonneg hsourceDensity_le with
    ⟨hpos_local, hbase_local⟩
  simpa [ρ, localSource] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (R := Rreg) (c := creg) (C := Creg)
      hRreg hcreg hCreg ht hCedge hbase
      (by simpa [localSource] using hpos_local)
      (by simpa [localSource, residualNegPowerIntegrableOn] using hbase_local)
      (by simpa [ρ, localSource] using hloss)
      (by simpa [ρ, localSource] using hdensity_nonneg)
      (by simpa [ρ, localSource] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Retained-passive signed-box handoff from monomial-times-unit residual and
source-density data.

Compared with
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialLower`,
this theorem derives the residual lower bound and source-density bounds from
supplied monomial-unit identities and unit bounds on the signed box.  The
source chart, weighted pushforward, unit identities, and local loss/density
bounds remain hypotheses. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialUnits
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
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
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {residualUnit densityUnit : (ι → ℝ) → ℝ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hCedge : Continuous Cedge)
    (hbase :
      Cedge x₀ =
        fun p : Fin (M + 1) ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict
          (paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hdensityUnit_aemeas :
      AEMeasurable densityUnit
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hres_eq : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)) =
        residualUnit y * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)))
    (hsourceDensity_eq : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y =
        densityUnit y * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hresUnit_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres ≤ residualUnit y)
    (hdensityUnit_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ densityUnit y)
    (hdensityUnit_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      densityUnit y ≤ Cres)
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
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            creg * (aoyagiCoordinateSquareSum
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
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
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
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            density (x, u) ≤ Creg) :
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
          ((Metric.ball (0 : EuclideanSpace ℝ ρ) Rreg).indicator
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
  rcases
      signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
        (residual := fun y : ι → ℝ =>
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
        (sourceDensity := sourceDensity)
        (residualUnit := residualUnit) (densityUnit := densityUnit)
        (R := Rres) (h := hres) (k := kres) (c := cres) (C := Cres)
        hdensityUnit_aemeas hres_eq hsourceDensity_eq hresUnit_lower
        hdensityUnit_nonneg hdensityUnit_le with
    ⟨hsourceDensity_aemeas, hres_lower, hsourceDensity_nonneg, hsourceDensity_le⟩
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialLower
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (sourceChart := sourceChart)
      (sourceDensity := sourceDensity) (loss := loss) (density := density)
      (t := t) (Rreg := Rreg) (creg := creg) (Creg := Creg)
      (cres := cres) (Cres := Cres) (Rres := Rres) (hres := hres) (kres := kres)
      hRreg hcreg hCreg ht hCedge hbase hsourceDensity_aemeas hsourceChart hmap
      hcres hCres hRres hcrit hres_lower hsourceDensity_nonneg hsourceDensity_le
      (by simpa [ρ] using hloss)
      (by simpa [ρ] using hdensity_nonneg)
      (by simpa [ρ] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Retained-passive signed-box handoff specialized to the selected-entry
center-coordinate monomial-unit package.

The selected-entry finite calculation supplies the residual/source-density
monomial identities and unit bounds.  The retained-passive source chart,
weighted pushforward, residual readout, and local loss/density bounds remain
explicit hypotheses. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [DecidableEq ι]
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {center : Finset ι} (pivot : center) {x₀ : α}
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
    {sourceChart : (center → ℝ) → α}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg : ℝ}
    {Rres : center → ℝ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hCedge : Continuous Cedge)
    (hbase :
      Cedge x₀ =
        fun p : Fin (M + 1) ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict
          (paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U₀ hU₀ Cedge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : center → ℝ =>
              ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y))))
    (hRres : ∀ i, 0 < Rres i)
    (hcrit_pivot :
      2 * t < ((center.erase pivot.1).card : ℝ) + 1)
    (hresidual_eq :
      ∀ y : center → ℝ,
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)) =
        SelectedEntrySignedBox.CenterCoord.residual pivot y)
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
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            creg * (aoyagiCoordinateSquareSum
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
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
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
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            density (x, u) ≤ Creg) :
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
          ((Metric.ball (0 : EuclideanSpace ℝ ρ) Rreg).indicator
            (fun u =>
              (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount (M + 1) H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last (M + 1)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  have hcrit :
      ∀ i : center,
        2 * t * (SelectedEntrySignedBox.CenterCoord.lossExp pivot i : ℝ) <
          (SelectedEntrySignedBox.CenterCoord.densityExp pivot i : ℝ) + 1 := by
    intro i
    by_cases hi : i = pivot
    · subst i
      simpa [SelectedEntrySignedBox.CenterCoord.lossExp,
        SelectedEntrySignedBox.CenterCoord.densityExp, mul_assoc] using hcrit_pivot
    · simp [SelectedEntrySignedBox.CenterCoord.lossExp,
        SelectedEntrySignedBox.CenterCoord.densityExp, hi]
  have hres_eq :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)) =
          SelectedEntrySignedBox.CenterCoord.residualUnit pivot y *
            ∏ i, |y i| ^
              (2 * (SelectedEntrySignedBox.CenterCoord.lossExp pivot i : ℝ)) :=
    Filter.Eventually.of_forall fun y => by
      rw [hresidual_eq y]
      exact SelectedEntrySignedBox.CenterCoord.residual_eq_unit_mul_abs_monomial pivot y
  have hsourceDensity_eq :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y =
          SelectedEntrySignedBox.CenterCoord.densityUnit pivot y *
            ∏ i, |y i| ^
              (SelectedEntrySignedBox.CenterCoord.densityExp pivot i : ℝ) :=
    Filter.Eventually.of_forall fun y =>
      SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_unit_mul_abs_monomial pivot y
  have hresUnit_lower :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        1 ≤ SelectedEntrySignedBox.CenterCoord.residualUnit pivot y :=
    Filter.Eventually.of_forall fun y =>
      SelectedEntrySignedBox.CenterCoord.one_le_residualUnit pivot y
  have hdensityUnit_nonneg :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        0 ≤ SelectedEntrySignedBox.CenterCoord.densityUnit pivot y :=
    Filter.Eventually.of_forall fun y =>
      SelectedEntrySignedBox.CenterCoord.densityUnit_nonneg pivot y
  have hdensityUnit_le :
      ∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
        SelectedEntrySignedBox.CenterCoord.densityUnit pivot y ≤ 1 :=
    Filter.Eventually.of_forall fun y =>
      SelectedEntrySignedBox.CenterCoord.densityUnit_le_one pivot y
  simpa [ρ] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialUnits
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (sourceChart := sourceChart)
      (sourceDensity := SelectedEntrySignedBox.CenterCoord.sourceDensity pivot)
      (residualUnit := SelectedEntrySignedBox.CenterCoord.residualUnit pivot)
      (densityUnit := SelectedEntrySignedBox.CenterCoord.densityUnit pivot)
      (loss := loss) (density := density)
      (t := t) (Rreg := Rreg) (creg := creg) (Creg := Creg)
      (cres := 1) (Cres := 1) (Rres := Rres)
      (hres := SelectedEntrySignedBox.CenterCoord.densityExp pivot)
      (kres := SelectedEntrySignedBox.CenterCoord.lossExp pivot)
      hRreg hcreg hCreg ht hCedge hbase hsourceChart hmap
      (by norm_num) (by norm_num) hRres hcrit
      (SelectedEntrySignedBox.CenterCoord.densityUnit_aemeasurable pivot Rres)
      hres_eq hsourceDensity_eq hresUnit_lower
      hdensityUnit_nonneg hdensityUnit_le
      (by simpa [ρ] using hloss)
      (by simpa [ρ] using hdensity_nonneg)
      (by simpa [ρ] using hdensity_le)

end PaperEndpointFixedBaseRegularCoordinateSourceData

end RetainedPassiveLocalMeasure

end Aoyagi
end DLN
end DLNFibre
