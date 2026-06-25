import DLNFibre.DLN.Aoyagi.ChainMapLossBridge
import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates

/-!
# Comparing adapted endpoint loss with original endpoint loss

This file connects the fixed adapted endpoint Frobenius loss used in the
Aoyagi product-reduction chart to the original endpoint Frobenius loss in an
arbitrary fixed pair of endpoint bases.  The comparison is only finite
basis-change linear algebra.  It does not construct charts, transport
densities, prove normal crossings, or extract an RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open Matrix DLNFibre.Core

section EndpointLossComparison

variable {N : ℕ}
variable {V : Fin (N + 1) → Type*}
variable [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]
variable {d : Fin (N + 1) → ℕ}

/-- The chain-map Frobenius loss is the coordinate square-sum of the matrix of
the difference linear map. -/
theorem chainMapMatrixFrobeniusLoss_eq_toMatrix_sub_squareSum
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (T T₀ : V 0 →ₗ[ℝ] V (Fin.last N)) :
    chainMapMatrixFrobeniusLoss b T T₀ =
      aoyagiCoordinateSquareSum
        (fun ij : Fin (d (Fin.last N)) × Fin (d 0) =>
          (LinearMap.toMatrix (b 0) (b (Fin.last N)) (T - T₀)) ij.1 ij.2) := by
  classical
  let M : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last N)) (T - T₀)
  have hM :
      LinearMap.toMatrix (b 0) (b (Fin.last N)) T -
          LinearMap.toMatrix (b 0) (b (Fin.last N)) T₀ = M := by
    ext i j
    simp [M]
  rw [chainMapMatrixFrobeniusLoss, chainMapMatrixFrobeniusLossAgainst]
  rw [hM]
  simpa [M] using matrix_trace_transpose_mul_self_eq_aoyagiCoordinateSquareSum (M := M)

universe v

variable
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc)

/-- The fixed adapted endpoint Frobenius loss is bounded above, up to a
positive scalar, by the same endpoint product-difference Frobenius loss in any
fixed original endpoint bases.

The constant depends only on the two pairs of endpoint bases. -/
theorem exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_chainMapFrobeniusLoss
    [∀ j, FiniteDimensional ℝ (W j)]
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
    (U₀ : Submodule ℝ (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    {α : Type*}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : α,
        c * paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
            W B U₀ hU₀ Cedge x ≤
          chainMapMatrixFrobeniusLoss b
            (chainMap (reverseVertex W)
              (fun p : Fin N =>
                (Cedge x p :
                  reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))
              0 (Fin.last N) (Fin.zero_le (Fin.last N)))
            (chainMap (reverseVertex W) (reverseEdge W B)
              0 (Fin.last N) (Fin.zero_le (Fin.last N))) := by
  classical
  let badapt : ∀ j, Module.Basis
      (Fin (Module.finrank ℝ U₀) ⊕
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ j)
      ℝ (reverseVertex W j) :=
    fun j ↦ paperEndpointFixedBaseBasis W B U₀ hU₀ j
  rcases
      exists_pos_const_forall_linearMap_toMatrix_squareSum_le_of_basis_change
        (bE := badapt 0) (bE' := b 0)
        (bF := badapt (Fin.last N)) (bF' := b (Fin.last N)) with
    ⟨c, hc_pos, hc⟩
  refine ⟨c, hc_pos, ?_⟩
  intro x
  let E : ∀ p : Fin N,
      reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ :=
    fun p ↦
      (Cedge x p :
        reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)
  let T : reverseVertex W 0 →ₗ[ℝ] reverseVertex W (Fin.last N) :=
    chainMap (reverseVertex W) E 0 (Fin.last N) (Fin.zero_le (Fin.last N))
  let T₀ : reverseVertex W 0 →ₗ[ℝ] reverseVertex W (Fin.last N) :=
    chainMap (reverseVertex W) (reverseEdge W B)
      0 (Fin.last N) (Fin.zero_le (Fin.last N))
  let f : reverseVertex W 0 →ₗ[ℝ] reverseVertex W (Fin.last N) := T - T₀
  have hadapt :
      paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
          W B U₀ hU₀ Cedge x =
        aoyagiCoordinateSquareSum
          (fun ij :
            ((Fin (Module.finrank ℝ U₀) ⊕
                throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) ×
              (Fin (Module.finrank ℝ U₀) ⊕
                throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0)) =>
            (LinearMap.toMatrix (badapt 0) (badapt (Fin.last N)) f)
              ij.1 ij.2) := by
    rw [paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) (x := x)]
    have hbaseRel :=
      paperEndpointFixedBaseAdaptedProductDifferenceSquareSum_eq_baseRelative_totalMatrix_squareSum
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := Cedge) (x := x)
    rw [hbaseRel]
    congr with ij
    simp [paperEndpointFixedBaseTotalMatrixOfReverseEdges, badapt, E, T, T₀, f]
  have horig :
      chainMapMatrixFrobeniusLoss b T T₀ =
        aoyagiCoordinateSquareSum
          (fun ij : Fin (d (Fin.last N)) × Fin (d 0) =>
            (LinearMap.toMatrix (b 0) (b (Fin.last N)) f) ij.1 ij.2) := by
    simpa [f] using
      chainMapMatrixFrobeniusLoss_eq_toMatrix_sub_squareSum
        (b := b) T T₀
  simpa [hadapt, horig, E, T, T₀, f] using hc f

/-- Original `lossDLN` form of the fixed-basis endpoint comparison for a
chain-coordinate tuple. -/
theorem exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
    [∀ j, FiniteDimensional ℝ (W j)]
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
    (U₀ : Submodule ℝ (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    {α : Type*}
    (Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : α,
        c * paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
            W B U₀ hU₀ Cedge x ≤
          lossDLN d
            (LinearMap.toMatrix (b 0) (b (Fin.last N))
              (chainMap (reverseVertex W) (reverseEdge W B)
                0 (Fin.last N) (Fin.zero_le (Fin.last N))))
            (chainMapMatrixTuple b
              (fun p : Fin N =>
                (Cedge x p :
                  reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))) := by
  rcases
      exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_chainMapFrobeniusLoss
        (W := W) (B := B) b U₀ hU₀ Cedge with
    ⟨c, hc_pos, hc⟩
  refine ⟨c, hc_pos, ?_⟩
  intro x
  rw [lossDLN_chainMapMatrixTuple_eq_chainMapFrobenius]
  exact hc x

end EndpointLossComparison

end Aoyagi
end DLN
end DLNFibre
