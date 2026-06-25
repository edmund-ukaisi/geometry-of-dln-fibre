import DLNFibre.DLN.Aoyagi.EndpointLossComparison
import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff

/-!
# Source-measure handoffs for original square-Frobenius loss

This file turns the self-base source-filter lower bound for original
`lossDLN` into restricted-source a.e. statements.  It is only local measure
plumbing; it does not construct the p.13 product chart, identify a regular
fiber variable, transport density/Jacobian factors, or extract an RLCT.
-/

noncomputable section

open MeasureTheory

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

section OriginalLossSourceMeasure

universe v

variable {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc)

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- The self-base original square-Frobenius lower bound becomes an a.e. lower
bound after restricting any base measure to a sufficiently small measurable
source neighborhood.

This is the original `lossDLN` analogue of the adapted-square-sum source
measure handoff.  It is still only a one-parameter source statement. -/
theorem exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase
    [∀ j, FiniteDimensional ℝ (W j)]
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
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
      Cedge x₀ = fun p : Fin N =>
        LinearMap.toContinuousLinearMap (reverseEdge W B p))
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
            lossDLN d
              (LinearMap.toMatrix (b 0) (b (Fin.last N))
                (chainMap (reverseVertex W) (reverseEdge W B)
                  0 (Fin.last N) (Fin.zero_le (Fin.last N))))
              (chainMapMatrixTuple b
                (fun p : Fin N =>
                  (Cedge x p :
                    reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))) := by
  rcases
      exists_pos_const_half_regular_add_residual_squareSum_eventually_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_source
        (W := W) (B := B) b sourceData hCedge hbase with
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
/-- Product-measure first-projection form of the self-base original
square-Frobenius source-measure handoff.  The asserted comparison is still
only a property of the base/source coordinate `z.1`. -/
theorem exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase
    [∀ j, FiniteDimensional ℝ (W j)]
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
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
      Cedge x₀ = fun p : Fin N =>
        LinearMap.toContinuousLinearMap (reverseEdge W B p))
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
            lossDLN d
              (LinearMap.toMatrix (b 0) (b (Fin.last N))
                (chainMap (reverseVertex W) (reverseEdge W B)
                  0 (Fin.last N) (Fin.zero_le (Fin.last N))))
              (chainMapMatrixTuple b
                (fun p : Fin N =>
                  (Cedge z.1 p :
                    reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))) := by
  rcases
      exists_pos_const_half_regular_add_residual_squareSum_eventually_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_source
        (W := W) (B := B) b sourceData hCedge hbase with
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
/-- Continuous-edge form of the self-base original square-Frobenius
source-measure handoff.  Global continuity supplies source-stratum
measurability and the self-base `ContinuousAt` input. -/
theorem exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_of_continuousEdge
    [∀ j, FiniteDimensional ℝ (W j)]
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
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
    (hCedge : Continuous Cedge)
    (hbase :
      Cedge x₀ = fun p : Fin N =>
        LinearMap.toContinuousLinearMap (reverseEdge W B p))
    {μ : Measure α} :
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
            lossDLN d
              (LinearMap.toMatrix (b 0) (b (Fin.last N))
                (chainMap (reverseVertex W) (reverseEdge W B)
                  0 (Fin.last N) (Fin.zero_le (Fin.last N))))
              (chainMapMatrixTuple b
                (fun p : Fin N =>
                  (Cedge x p :
                    reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))) := by
  have hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge) := by
    exact
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
        (W := W) (B := B) (Cedge := Cedge) (r := r) (rEdge := rEdge) hCedge
  exact
    exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase
      (W := W) (B := B) b sourceData hCedge.continuousAt hbase hsource_meas

set_option linter.unusedSectionVars false in
/-- Continuous-edge product-measure first-projection form of the self-base
original square-Frobenius source-measure handoff. -/
theorem exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_of_continuousEdge
    [∀ j, FiniteDimensional ℝ (W j)]
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
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
    (hCedge : Continuous Cedge)
    (hbase :
      Cedge x₀ = fun p : Fin N =>
        LinearMap.toContinuousLinearMap (reverseEdge W B p))
    {μ : Measure α} {ν : Measure β} :
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
            lossDLN d
              (LinearMap.toMatrix (b 0) (b (Fin.last N))
                (chainMap (reverseVertex W) (reverseEdge W B)
                  0 (Fin.last N) (Fin.zero_le (Fin.last N))))
              (chainMapMatrixTuple b
                (fun p : Fin N =>
                  (Cedge z.1 p :
                    reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))) := by
  have hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge) := by
    exact
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
        (W := W) (B := B) (Cedge := Cedge) (r := r) (rEdge := rEdge) hCedge
  exact
    exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase
      (W := W) (B := B) b sourceData hCedge.continuousAt hbase hsource_meas

end PaperEndpointFixedBaseRegularCoordinateSourceData

end OriginalLossSourceMeasure

end Aoyagi
end DLN
end DLNFibre

end
