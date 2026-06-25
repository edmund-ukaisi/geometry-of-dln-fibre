import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.MonomialChartIntegrability
import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
import DLNFibre.DLN.Aoyagi.RegularSuspensionSquareSumIntegrability
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Local a.e. handoffs for p. 13 regular-suspension source comparisons

This file packages source-neighborhood p. 13 square-sum comparisons as
restricted-measure a.e. facts.  It also composes supplied local product
loss/density and residual integrability hypotheses with the finite-side p. 13
regular-coordinate adapter.  It does not construct Aoyagi's p. 13 product
chart, identify the auxiliary product fiber with regular coordinates, compare
an original DLN loss, transport density/Jacobian factors, prove the residual
base hypotheses, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

section FixedBaseRealLocalMeasure

variable {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc)

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- The source-stratum half lower bound becomes an a.e. lower bound after
restricting any base measure to a sufficiently small measurable source
neighborhood. -/
theorem exists_open_ae_restrict_source_literal_regular_add_residual_squareSum_half_le
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ x ∂ μ.restrict
          (U ∩ paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B Cedge r rEdge),
        (1 / 2 : ℝ) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x)) ≤
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    exists_open_ae_restrict_inter_of_eventually_nhdsWithin
      (μ := μ) (x₀ := x₀)
      (s := paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)
      hsource_meas
      (literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
        (W := W) (B := B) sourceData)

set_option linter.unusedSectionVars false in
/-- Product-measure first-projection form of
`exists_open_ae_restrict_source_literal_regular_add_residual_squareSum_half_le`.
The asserted comparison is still only a property of the base/source coordinate
`z.1`. -/
theorem exists_open_ae_restrict_source_prod_fst_literal_regular_add_residual_squareSum_half_le
    [∀ j, FiniteDimensional ℝ (W j)]
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [MeasurableSpace β] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α} {ν : Measure β}
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ z : α × β ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν,
        (1 / 2 : ℝ) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1)) ≤
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge z.1) := by
  exact
    exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
      (μ := μ) (ν := ν) (x₀ := x₀)
      (s := paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)
      hsource_meas
      (literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
        (W := W) (B := B) sourceData)

set_option linter.unusedSectionVars false in
/-- A supplied local lower bound of a base loss by the literal p. 13 square-sum
becomes an a.e. lower bound by the regular-plus-residual cleaned square-sum
after restricting to a small measurable source neighborhood. -/
theorem exists_open_ae_restrict_source_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α} {loss : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        c * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤ loss x) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ x ∂ μ.restrict
          (U ∩ paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B Cedge r rEdge),
        (c / 2) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge x)) ≤ loss x := by
  exact
    exists_open_ae_restrict_inter_of_eventually_nhdsWithin
      (μ := μ) (x₀ := x₀)
      (s := paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)
      hsource_meas
      (const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
        (W := W) (B := B) sourceData hc hloss)

set_option linter.unusedSectionVars false in
/-- Product-measure first-projection form of the supplied base-loss handoff.
The loss here is still a base function `loss z.1`; this does not identify an
auxiliary product fiber with p. 13 regular coordinates. -/
theorem exists_open_ae_restrict_source_prod_fst_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
    [∀ j, FiniteDimensional ℝ (W j)]
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [MeasurableSpace β] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α} {ν : Measure β} {loss : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        c * aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) ≤ loss x) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ z : α × β ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν,
        (c / 2) *
          (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseRegularBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1) +
            aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1)) ≤ loss z.1 := by
  exact
    exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
      (μ := μ) (ν := ν) (x₀ := x₀)
      (s := paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)
      hsource_meas
      (const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
        (W := W) (B := B) sourceData hc hloss)

set_option linter.unusedSectionVars false in
/-- At a continuous fixed-base paper chain, the adapted fixed-base
product-difference comparison becomes an a.e. lower bound after restricting to
a small measurable source neighborhood.

The right-hand side is the adapted fixed-base product-difference square-sum,
not the original DLN/statistical loss. -/
theorem exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    {μ : Measure α}
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)) :
    ∃ c : ℝ, 0 < c ∧
      ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
        ∀ᵐ x ∂ μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge),
          (c / 2) *
            (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseRegularBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ Cedge x := by
  rcases
      exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
        (W := W) (B := B) sourceData hCedge hbase with
    ⟨c, hc_pos, hbound⟩
  rcases
      exists_open_ae_restrict_inter_of_eventually_nhdsWithin
        (μ := μ) (x₀ := x₀)
        (s := paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge)
        hsource_meas hbound with
    ⟨U, hUopen, hx₀U, hUbound⟩
  exact ⟨c, hc_pos, U, hUopen, hx₀U, hUbound⟩

set_option linter.unusedSectionVars false in
/-- Product-measure first-projection form of the self-base adapted
product-difference local-measure handoff.  The asserted comparison is only a
property of the base/source coordinate `z.1`. -/
theorem exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
    [∀ j, FiniteDimensional ℝ (W j)]
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [MeasurableSpace β] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    {μ : Measure α} {ν : Measure β}
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge)) :
    ∃ c : ℝ, 0 < c ∧
      ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
        ∀ᵐ z : α × β ∂
            (μ.restrict
              (U ∩ paperEndpointFixedBaseSourceRankStratum
                (K := ℝ) W B Cedge r rEdge)).prod ν,
          (c / 2) *
            (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseRegularBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge z.1) +
              aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge z.1)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ Cedge z.1 := by
  rcases
      exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
        (W := W) (B := B) sourceData hCedge hbase with
    ⟨c, hc_pos, hbound⟩
  rcases
      exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
        (μ := μ) (ν := ν) (x₀ := x₀)
        (s := paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge)
        hsource_meas hbound with
    ⟨U, hUopen, hx₀U, hUbound⟩
  exact ⟨c, hc_pos, U, hUopen, hx₀U, hUbound⟩

set_option linter.unusedSectionVars false in
/-- Uniform-in-fiber source-filter bounds become product-measure a.e. bounds
after restricting the base to a sufficiently small measurable source
neighborhood.

This is the handoff shape expected by the finite-side p.13 regular-coordinate
integrability adapter for its loss and density hypotheses.  It does not prove
those source-filter bounds, residual positivity, residual negative-power
integrability, or any product chart/density transport theorem. -/
theorem exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {R c C : ℝ}
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∀ᵐ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν,
        z.2 ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge z.1) +
            aoyagiCoordinateSquareSum (fun i => z.2 i)) ≤ loss z) ∧
      (∀ᵐ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν,
        z.2 ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
          0 ≤ density z) ∧
      (∀ᵐ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν,
        z.2 ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
          density z ≤ C) := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  have hbounds :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        (∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) ∧
        (∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            0 ≤ density (x, u)) ∧
        (∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            density (x, u) ≤ C) := by
    filter_upwards [hloss, hdensity_nonneg, hdensity_le] with x hxloss hxdensity_nonneg
      hxdensity_le
    exact ⟨by simpa [ρ, sourceStratum] using hxloss,
      by simpa [ρ, sourceStratum] using hxdensity_nonneg,
      by simpa [ρ, sourceStratum] using hxdensity_le⟩
  rcases exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
      (μ := μ) (ν := ν) (x₀ := x₀) (s := sourceStratum)
      (by simpa [sourceStratum] using hsource_meas) hbounds with
    ⟨U, hUopen, hxU, hbounds_ae⟩
  refine ⟨U, hUopen, hxU, ?_, ?_, ?_⟩
  · filter_upwards [hbounds_ae] with z hz hzball
    exact hz.1 z.2 hzball
  · filter_upwards [hbounds_ae] with z hz hzball
    exact hz.2.1 z.2 hzball
  · filter_upwards [hbounds_ae] with z hz hzball
    exact hz.2.2 z.2 hzball

set_option linter.unusedSectionVars false in
/-- Finite residual negative-power integral over a supplied base set.  This is
only a notation wrapper for the base-side integrability hypothesis consumed by
the p. 13 regular-coordinate finite-side adapter. -/
def residualNegPowerIntegrableOn
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ)
    (source : Set α) (μ : Measure α) (t : ℝ) : Prop :=
  (∫⁻ x : α, ENNReal.ofReal
    ((aoyagiCoordinateSquareSum
      (paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t))
      ∂ (μ.restrict source)) < ∞

set_option linter.unusedSectionVars false in
/-- The residual square-sum is positive a.e. once its zero locus is null for
the restricted source measure. -/
theorem residualSquareSum_pos_ae_of_zero_set_null
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α}
    (hzero :
      (μ.restrict source)
        {x | aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) = 0} = 0) :
    ∀ᵐ x ∂ μ.restrict source,
      0 < aoyagiCoordinateSquareSum
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge x) := by
  exact
    ae_pos_of_forall_nonneg_of_measure_zero_eq_zero
      (μ := μ.restrict source)
      (f := fun x =>
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
      (fun x =>
        aoyagiCoordinateSquareSum_nonneg
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
      hzero

set_option linter.unusedSectionVars false in
/-- Residual positivity and negative-power integrability restrict to smaller
source sets. -/
theorem residualSourceHypotheses_mono
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source source' : Set α} {μ : Measure α} {t : ℝ}
    (hsubset : source' ⊆ source)
    (hpos :
      ∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
    (hbase : residualNegPowerIntegrableOn
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t) :
    (∀ᵐ x ∂ μ.restrict source',
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source' μ t := by
  constructor
  · exact ae_mono (Measure.restrict_mono hsubset le_rfl) hpos
  · exact
      (lintegral_mono'
        (Measure.restrict_mono hsubset le_rfl)
        (le_refl (fun x : α => ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t))))).trans_lt
        (by simpa [residualNegPowerIntegrableOn] using hbase)

set_option linter.unusedSectionVars false in
/-- Residual positivity and negative-power integrability on a smaller source set
from residual negative-power integrability on a larger source set and nullity of
the residual zero locus there. -/
theorem residualSourceHypotheses_mono_of_zero_set_null
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [MeasurableSpace α]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source source' : Set α} {μ : Measure α} {t : ℝ}
    (hsubset : source' ⊆ source)
    (hzero :
      (μ.restrict source)
        {x | aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x) = 0} = 0)
    (hbase : residualNegPowerIntegrableOn
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t) :
    (∀ᵐ x ∂ μ.restrict source',
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source' μ t := by
  exact
    residualSourceHypotheses_mono
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (source' := source')
      (μ := μ) (t := t) hsubset
      (residualSquareSum_pos_ae_of_zero_set_null
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (source := source) (μ := μ) hzero)
      hbase

set_option linter.unusedSectionVars false in
/-- Residual positivity and negative-power integrability from an explicitly
supplied source-measure pushforward.

This is only measure-transport plumbing.  The chart map, the equality
`μ.restrict source = Measure.map chart ν`, residual positivity after pulling
back along the chart, and chart-side residual integrability are all supplied. -/
theorem residualSourceHypotheses_of_measure_map
    [∀ j, FiniteDimensional ℝ (W j)]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α} {ν : Measure β} {chart : β → α} {t : ℝ}
    (hchart : AEMeasurable chart ν)
    (hmap : μ.restrict source = Measure.map chart ν)
    (hpos_meas :
      MeasurableSet {x : α |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)})
    (hpos_chart :
      ∀ᵐ y ∂ ν,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
    (hbase_chart :
      (∫⁻ y : β, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y))) ^ (-t)) ∂ ν) < ∞) :
    (∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t := by
  constructor
  · have hpos_map :
        ∀ᵐ x ∂ Measure.map chart ν,
          0 < aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x) :=
      (ae_map_iff hchart hpos_meas).2 hpos_chart
    simpa [hmap] using hpos_map
  · have hle :
        (∫⁻ x : α, ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t))
            ∂ Measure.map chart ν) ≤
          (∫⁻ y : β, ENNReal.ofReal
            ((aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W B U₀ hU₀ Cedge (chart y))) ^ (-t)) ∂ ν) := by
      exact lintegral_map_le
        (fun x : α => ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge x)) ^ (-t)))
        chart
    exact lt_of_le_of_lt (by simpa [residualNegPowerIntegrableOn, hmap] using hle) hbase_chart

set_option linter.unusedSectionVars false in
/-- Residual source hypotheses from a signed-box chart pushforward and an
explicit absolute-monomial lower bound on the chart-side residual square.

This is an unweighted signed-box source-measure constructor.  It does not
construct the chart, prove the source-measure pushforward identity, transport a
Jacobian/density factor, compare the original DLN loss, or extract an RLCT. -/
theorem residualSourceHypotheses_of_measure_map_signedBox_monomialLower
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α}
    {chart : (ι → ℝ) → α} {t c : ℝ} {R : ι → ℝ} {k : ι → ℕ}
    (hchart : AEMeasurable chart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hmap :
      μ.restrict source =
        Measure.map chart
          (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hpos_meas :
      MeasurableSet {x : α |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)})
    (hc : 0 < c) (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < 1)
    (hlower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      c * ∏ i, (|y i|) ^ (2 * (k i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y))) :
    (∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t := by
  let signedBox : Measure (ι → ℝ) :=
    Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))
  have hpos_chart :
      ∀ᵐ y ∂ signedBox,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y)) := by
    have hcoord : ∀ᵐ y : ι → ℝ ∂ signedBox, ∀ i, 0 < |y i| := by
      dsimp [signedBox]
      exact ae_forall_abs_pos_measure_pi_restrict_Ioo_neg (R := R) (ι := ι)
    filter_upwards [hcoord, hlower] with y hyabs hylower
    have hmonomial_pos :
        0 < ∏ i, (|y i|) ^ (2 * (k i : ℝ)) := by
      exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hyabs i) _
    exact lt_of_lt_of_le (mul_pos hc hmonomial_pos) hylower
  have hbase_chart :
      (∫⁻ y : ι → ℝ, ENNReal.ofReal
        ((aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y))) ^ (-t))
          ∂ signedBox) < ∞ := by
    dsimp [signedBox]
    exact
      lintegral_ofReal_loss_rpow_neg_signedBox_lt_top
        (k := k) (t := t) (R := R) (c := c)
        (loss := fun y : ι → ℝ =>
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
        hc ht hR hcrit hlower
  exact
    residualSourceHypotheses_of_measure_map
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (μ := μ)
      (ν := signedBox) (chart := chart) (t := t)
      (by simpa [signedBox] using hchart)
      (by simpa [signedBox] using hmap)
      hpos_meas hpos_chart hbase_chart

set_option linter.unusedSectionVars false in
/-- Residual source hypotheses from a signed-box chart pushforward with a
supplied density and explicit absolute-monomial residual/density bounds.

This is a weighted signed-box source-measure constructor.  It assumes the
source-measure pushforward through `signedBox.withDensity (ofReal density)` and
the chart-side density bounds; it does not construct the chart, compute the
Jacobian/density factor, compare the original DLN loss, or extract an RLCT. -/
theorem residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α}
    {chart : (ι → ℝ) → α} {density : (ι → ℝ) → ℝ}
    {t c C : ℝ} {R : ι → ℝ} {h k : ι → ℕ}
    (hdensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (density y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hchart : AEMeasurable chart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hmap :
      μ.restrict source =
        Measure.map chart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (density y))))
    (hpos_meas :
      MeasurableSet {x : α |
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)})
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1)
    (hlower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      c * ∏ i, (|y i|) ^ (2 * (k i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
    (hdensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      0 ≤ density y)
    (hdensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      density y ≤ C * ∏ i, (|y i|) ^ (h i : ℝ)) :
    (∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t := by
  let signedBox : Measure (ι → ℝ) :=
    Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))
  let weightedBox : Measure (ι → ℝ) :=
    signedBox.withDensity (fun y : ι → ℝ => ENNReal.ofReal (density y))
  let residual : (ι → ℝ) → ℝ := fun y =>
    aoyagiCoordinateSquareSum
      (paperEndpointFixedBaseResidualBlockCoordinateMap
        (K := ℝ) W B U₀ hU₀ Cedge (chart y))
  have hpos_signed :
      ∀ᵐ y ∂ signedBox, 0 < residual y := by
    have hcoord : ∀ᵐ y : ι → ℝ ∂ signedBox, ∀ i, 0 < |y i| := by
      dsimp [signedBox]
      exact ae_forall_abs_pos_measure_pi_restrict_Ioo_neg (R := R) (ι := ι)
    filter_upwards [hcoord, hlower] with y hyabs hylower
    have hmonomial_pos :
        0 < ∏ i, (|y i|) ^ (2 * (k i : ℝ)) := by
      exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hyabs i) _
    exact lt_of_lt_of_le (mul_pos hc hmonomial_pos) hylower
  have hpos_chart :
      ∀ᵐ y ∂ weightedBox, 0 < residual y := by
    exact (withDensity_absolutelyContinuous signedBox
      (fun y : ι → ℝ => ENNReal.ofReal (density y))).ae_le hpos_signed
  have hfinite_signed :
      (∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t) * density y)
        ∂ signedBox) < ∞ := by
    dsimp [signedBox, residual]
    exact
      lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top
        (h := h) (k := k) (t := t) (R := R) (c := c) (C := C)
        (loss := fun y : ι → ℝ =>
          aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
        (density := density)
        hc hC ht hR hcrit hlower hdensity_nonneg hdensity_le
  have hbase_chart :
      (∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t)) ∂ weightedBox) < ∞ := by
    have hdensity_lt_top :
        ∀ᵐ y : ι → ℝ ∂ signedBox, ENNReal.ofReal (density y) < ∞ := by
      filter_upwards with y
      exact ENNReal.ofReal_lt_top
    have hwith :
        (∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t)) ∂ weightedBox) =
          ∫⁻ y : ι → ℝ,
            ENNReal.ofReal (density y) * ENNReal.ofReal ((residual y) ^ (-t))
            ∂ signedBox := by
      dsimp [weightedBox]
      rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀
        signedBox (by simpa [signedBox] using hdensity_aemeas) hdensity_lt_top
        (fun y : ι → ℝ => ENNReal.ofReal ((residual y) ^ (-t)))]
      simp [Pi.mul_apply]
    have hmul :
        (∫⁻ y : ι → ℝ,
            ENNReal.ofReal (density y) * ENNReal.ofReal ((residual y) ^ (-t))
            ∂ signedBox) =
          ∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t) * density y)
            ∂ signedBox := by
      apply lintegral_congr_ae
      filter_upwards [hdensity_nonneg] with y hyden_nonneg
      rw [mul_comm]
      exact (ENNReal.ofReal_mul' hyden_nonneg).symm
    calc
      (∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t)) ∂ weightedBox)
          = ∫⁻ y : ι → ℝ,
              ENNReal.ofReal (density y) * ENNReal.ofReal ((residual y) ^ (-t))
              ∂ signedBox := hwith
      _ = ∫⁻ y : ι → ℝ, ENNReal.ofReal ((residual y) ^ (-t) * density y)
            ∂ signedBox := hmul
      _ < ∞ := hfinite_signed
  exact
    residualSourceHypotheses_of_measure_map
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (μ := μ)
      (ν := weightedBox) (chart := chart) (t := t)
      (hchart.mono_ac (by
        simpa [signedBox, weightedBox] using
          withDensity_absolutelyContinuous signedBox
            (fun y : ι → ℝ => ENNReal.ofReal (density y))))
      (by simpa [signedBox, weightedBox] using hmap)
      hpos_meas
      (by simpa [residual] using hpos_chart)
      (by simpa [residual] using hbase_chart)

set_option linter.unusedSectionVars false in
/-- Weighted signed-box residual source hypotheses with the residual positive
set measurability derived from a measurable residual coordinate map. -/
theorem residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_residual
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α}
    {chart : (ι → ℝ) → α} {density : (ι → ℝ) → ℝ}
    {t c C : ℝ} {R : ι → ℝ} {h k : ι → ℕ}
    (hres_meas :
      Measurable
        (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W B U₀ hU₀ Cedge))
    (hdensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (density y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hchart : AEMeasurable chart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hmap :
      μ.restrict source =
        Measure.map chart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (density y))))
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1)
    (hlower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      c * ∏ i, (|y i|) ^ (2 * (k i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
    (hdensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      0 ≤ density y)
    (hdensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      density y ≤ C * ∏ i, (|y i|) ^ (h i : ℝ)) :
    (∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t := by
  exact
    residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (μ := μ)
      (chart := chart) (density := density)
      (t := t) (c := c) (C := C) (R := R) (h := h) (k := k)
      hdensity_aemeas hchart hmap
      (measurableSet_residualSquareSum_pos_of_measurable
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) hres_meas)
      hc hC ht hR hcrit hlower hdensity_nonneg hdensity_le

set_option linter.unusedSectionVars false in
/-- Weighted signed-box residual source hypotheses with residual positive-set
measurability derived from measurable fixed-basis edge matrices.

This consumes exactly the matrix-valued edge family used by the deterministic
p. 13 suffix recursion; it still assumes the signed-box chart, pushforward,
monomial residual lower bound, and density bounds. -/
theorem residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {source : Set α} {μ : Measure α}
    {chart : (ι → ℝ) → α} {density : (ι → ℝ) → ℝ}
    {t c C : ℝ} {R : ι → ℝ} {h k : ι → ℕ}
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hdensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (density y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hchart : AEMeasurable chart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))))
    (hmap :
      μ.restrict source =
        Measure.map chart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (density y))))
    (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : ∀ i, 2 * t * (k i : ℝ) < (h i : ℝ) + 1)
    (hlower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      c * ∏ i, (|y i|) ^ (2 * (k i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (chart y)))
    (hdensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      0 ≤ density y)
    (hdensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(R i)) (R i))),
      density y ≤ C * ∏ i, (|y i|) ^ (h i : ℝ)) :
    (∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x)) ∧
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge source μ t := by
  exact
    residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_residual
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := source) (μ := μ)
      (chart := chart) (density := density)
      (t := t) (c := c) (C := C) (R := R) (h := h) (k := k)
      (measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
        (W := W) (B := B) U₀ hU₀ Cedge hEdgeMatrix)
      hdensity_aemeas hchart hmap
      hc hC ht hR hcrit hlower hdensity_nonneg hdensity_le

set_option linter.unusedSectionVars false in
/-- Local finite-side p.13 regular-coordinate integrability from supplied
source-stratum residual integrability and supplied uniform-in-fiber loss/density
bounds.

This combines the uniform source-filter handoff in this file with the
finite-side bounded-density p.13 adapter from
`RegularSuspensionSquareSumIntegrability.lean`.  Residual positivity and
residual negative-power integrability are still explicit hypotheses on the
source rank stratum. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B Cedge r rEdge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge
        (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) μ t)
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  rcases exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds
      (W := W) (B := B) (x₀ := x₀) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (r := r) (rEdge := rEdge) (μ := μ) (ν := ν)
      (loss := loss) (density := density) (R := R) (c := c) (C := C)
      hsource_meas hloss hdensity_nonneg hdensity_le with
    ⟨U, hUopen, hxU, hloss_ae, hdensity_nonneg_ae, hdensity_le_ae⟩
  have hsubset : U ∩ sourceStratum ⊆ sourceStratum := Set.inter_subset_right
  rcases residualSourceHypotheses_mono
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (source := sourceStratum)
      (source' := U ∩ sourceStratum) (μ := μ) (t := t)
      hsubset hpos_source
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source) with
    ⟨hpos_U, hbase_U⟩
  have hfin :=
    lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top
      (W := W) (B := B) sourceData
      (μ := μ.restrict (U ∩ sourceStratum)) (ν := ν)
      (loss := loss) (density := density) (t := t) (R := R)
      (c := c) (C := C) hR hc hC ht hpos_U
      (by simpa [residualNegPowerIntegrableOn] using hbase_U)
      (by simpa [ρ, sourceStratum] using hloss_ae)
      (by simpa [ρ, sourceStratum] using hdensity_nonneg_ae)
      (by simpa [ρ, sourceStratum] using hdensity_le_ae)
  exact ⟨U, hUopen, hxU, by simpa [ρ, sourceStratum] using hfin⟩

set_option linter.unusedSectionVars false in
/-- Local finite-integral handoff with residual source hypotheses supplied by
a weighted signed-box residual chart.

This composes the signed-box residual source-measure constructor with the
p.13 local finite-integral bridge.  It still assumes source-stratum
measurability, the signed-box pushforward and monomial bounds, and the local
regular-fiber loss/density bounds. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rreg creg Creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRreg : 0 < Rreg) (hcreg : 0 < creg) (hCreg : 0 ≤ Creg) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) =
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
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg →
            density (x, u) ≤ Creg) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) Rreg).indicator
            (fun u =>
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B Cedge r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  rcases
      residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (source := sourceStratum) (μ := μ)
        (chart := sourceChart) (density := sourceDensity)
        (t := t) (c := cres) (C := Cres) (R := Rres) (h := hres) (k := kres)
        hEdgeMatrix hsourceDensity_aemeas hsourceChart
        (by simpa [sourceStratum] using hmap)
        hcres hCres (le_of_lt ht) hRres hcrit hres_lower
        hsourceDensity_nonneg hsourceDensity_le with
    ⟨hpos_source, hbase_source⟩
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (R := Rreg) (c := creg) (C := Creg)
      hRreg hcreg hCreg ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      (by simpa [ρ, sourceStratum] using hloss)
      (by simpa [ρ, sourceStratum] using hdensity_nonneg)
      (by simpa [ρ, sourceStratum] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Conditional p.13 finite-integral handoff for a chart loss identified with
the adapted fixed-base product-difference square-sum.

The product-coordinate lower bound and the identification of the chart loss
with the adapted square-sum are explicit hypotheses.  This theorem does not
construct the product chart or compare with the original DLN/statistical
loss. -/
theorem exists_open_lintegral_ofReal_chartLoss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_identified
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ CedgeBase H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {chartLoss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B CedgeBase r rEdge))
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B CedgeBase r rEdge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeBase x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) CedgeBase
        (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge) μ t)
    (hadapted_lower :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
    (hloss_id :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) = chartLoss (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)),
        ENNReal.ofReal
          ((Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
            (fun u =>
              (chartLoss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict
            (U ∩ paperEndpointFixedBaseSourceRankStratum
              (K := ℝ) W B CedgeBase r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B CedgeBase r rEdge
  have hloss :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ chartLoss (x, u) := by
    filter_upwards [hadapted_lower, hloss_id] with x hxlower hxid u hu
    calc
      c * (aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W B U₀ hU₀ CedgeBase x) +
          aoyagiCoordinateSquareSum (fun i => u i))
          ≤ paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) := hxlower u hu
      _ = chartLoss (x, u) := hxid u hu
  exact
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := chartLoss) (density := density)
      (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      (by simpa [ρ, sourceStratum] using hloss)
      (by simpa [ρ, sourceStratum] using hdensity_nonneg)
      (by simpa [ρ, sourceStratum] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Local finite-side p.13 integrability when the transported density factor is
supplied as a positive continuous function at the chart center.

This removes the separate local nonnegativity and boundedness hypotheses for
the density by shrinking the regular-coordinate radius.  It still does not
construct the density/Jacobian factor or prove the loss lower bound. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax c : ℝ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B Cedge r rEdge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) Cedge
        (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) μ t)
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) :
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          ENNReal.ofReal
            ((Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict
              (U ∩ paperEndpointFixedBaseSourceRankStratum
                (K := ℝ) W B Cedge r rEdge)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  rcases exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
      (s := sourceStratum) (Rmax := Rmax) hdensity_cont hdensity_pos hRmax with
    ⟨R, C, hR, hRle, hC, hdensity_nonneg, hdensity_le⟩
  have hloss_R :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u) := by
    filter_upwards [hloss] with x hx u hu
    exact hx u (Metric.ball_subset_ball hRle hu)
  rcases exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (R := R) (c := c) (C := C)
      hR hc hC ht hsource_meas hpos_source hbase_source
      (by simpa [ρ, sourceStratum] using hloss_R)
      (by simpa [ρ, sourceStratum] using hdensity_nonneg)
      (by simpa [ρ, sourceStratum] using hdensity_le) with
    ⟨U, hUopen, hxU, hfin⟩
  exact ⟨R, C, U, hR, hRle, hC, hUopen, hxU, by simpa [ρ, sourceStratum] using hfin⟩

set_option linter.unusedSectionVars false in
/-- Radius-shrinking local finite-integral handoff with residual source
hypotheses supplied by a weighted signed-box residual chart and density bounds
supplied by positivity and continuity at the chart center.

This composes the signed-box residual source-measure constructor with the
continuous-density p.13 local finite-integral bridge.  It still assumes
source-stratum measurability, the signed-box pushforward and monomial bounds,
the density factor itself, and the local regular-fiber loss lower bound. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (hcreg : 0 < creg) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge))
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) =
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
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  rcases
      residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (source := sourceStratum) (μ := μ)
        (chart := sourceChart) (density := sourceDensity)
        (t := t) (c := cres) (C := Cres) (R := Rres) (h := hres) (k := kres)
        hEdgeMatrix hsourceDensity_aemeas hsourceChart
        (by simpa [sourceStratum] using hmap)
        hcres hCres (le_of_lt ht) hRres hcrit hres_lower
        hsourceDensity_nonneg hsourceDensity_le with
    ⟨hpos_source, hbase_source⟩
  simpa [ρ, sourceStratum] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (Rmax := Rmax) (c := creg)
      hRmax hcreg ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      hdensity_cont hdensity_pos
      (by simpa [ρ, sourceStratum] using hloss)

set_option linter.unusedSectionVars false in
/-- Radius-shrinking local finite-integral handoff from a globally continuous
edge family, a weighted signed-box residual chart, and a positive continuous
density factor.

Global continuity of `Cedge` supplies both source-stratum measurability and
measurability of the fixed-basis endpoint edge matrices consumed by the
deterministic p.13 suffix recursion.  The signed-box chart, weighted
pushforward, residual monomial bound, density factor, and loss lower bound are
still explicit hypotheses. -/
theorem exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {loss density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax creg cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (hcreg : 0 < creg) (ht : 0 < t)
    (hCedge : Continuous Cedge)
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) =
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
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hloss :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            creg * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤ loss (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (loss (z.1, u)) ^
                  (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  have hsource_meas : MeasurableSet sourceStratum := by
    simpa [sourceStratum] using
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
        (W := W) (B := B) (Cedge := Cedge) (r := r) (rEdge := rEdge) hCedge
  have hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))) := by
    refine (continuous_pi ?_).measurable
    intro p
    have hCedge_p : Continuous fun x : α ↦ Cedge x p :=
      (continuous_apply p).comp hCedge
    have hcoord : Continuous
        (fun f : reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ ↦
          LinearMap.toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
            (f : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)) :=
      continuous_linearMap_toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
    simpa [paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using hcoord.comp hCedge_p
  simpa [ρ, sourceStratum] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_continuousAt_pos_density
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (loss := loss) (density := density)
      (t := t) (Rmax := Rmax) (creg := creg) (cres := cres) (Cres := Cres)
      (Rres := Rres) (hres := hres) (kres := kres)
      hRmax hcreg ht hsource_meas hEdgeMatrix
      hsourceDensity_aemeas hsourceChart
      (by simpa [sourceStratum] using hmap)
      hcres hCres hRres hcrit hres_lower
      hsourceDensity_nonneg hsourceDensity_le
      hdensity_cont hdensity_pos
      (by simpa [ρ, sourceStratum] using hloss)

end PaperEndpointFixedBaseRegularCoordinateSourceData

end FixedBaseRealLocalMeasure

end Aoyagi
end DLN
end DLNFibre

end
