import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates

/-!
# Local a.e. handoffs for p. 13 regular-suspension source comparisons

This file packages source-neighborhood p. 13 square-sum comparisons as
restricted-measure a.e. facts.  It is only a source-filter-to-measure handoff:
it does not construct Aoyagi's p. 13 product chart, identify the auxiliary
product fiber with regular coordinates, compare an original DLN loss, transport
density/Jacobian factors, prove integrability, or extract an RLCT.
-/

noncomputable section

open MeasureTheory

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

end PaperEndpointFixedBaseRegularCoordinateSourceData

end FixedBaseRealLocalMeasure

end Aoyagi
end DLN
end DLNFibre

end
