import DLNFibre.DLN.Aoyagi.BasepointCertificate

/-!
# Variable chains in fixed endpoint basepoint coordinates

This file fixes the adapted endpoint bases chosen from a base paper-order chain
`B` and expresses a variable paper-order chain `C` in those same bases.  It
does not assert that exact rank strata are open, that bases vary with `C`, or
that the hypotheses of Aoyagi's product-reduction induction hold automatically.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

section FixedBase

universe u v

variable {K : Type u} [Field K] {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  (B C : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

/-- The endpoint adapted basis at one reversed vertex, fixed from the base chain `B`. -/
abbrev paperEndpointFixedBaseBasis
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (j : Fin (N + 1)) :
    Module.Basis
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
      K (reverseVertex W j) :=
  throughSubspaceAdaptedBasis (reverseVertex W) (reverseEdge W B) U₀
    (paperEndpointReverseIsCompl W B U₀ hU₀).disjoint
    (paperEndpointChartData W B U₀ hU₀) j

/-- A variable reversed chain segment expressed in the endpoint bases fixed from `B`. -/
def paperEndpointFixedBaseChainMapMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ i) K :=
  LinearMap.toMatrix
    (paperEndpointFixedBaseBasis W B U₀ hU₀ i)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ j)
    (chainMap (reverseVertex W) (reverseEdge W C) i j hij)

/-- One variable paper-order edge expressed in the endpoint bases fixed from `B`. -/
def paperEndpointFixedBaseEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
  LinearMap.toMatrix
    (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
    (reverseEdge W C p)

/-- The variable total paper product expressed in the endpoint bases fixed from `B`. -/
def paperEndpointFixedBaseTotalMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K :=
  LinearMap.toMatrix
    (paperEndpointFixedBaseBasis W B U₀ hU₀ 0)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ (Fin.last N))
    (paperTotalMap W C)

set_option linter.unusedDecidableInType false in
/-- In fixed basepoint bases, an empty variable chain segment has identity matrix. -/
theorem paperEndpointFixedBaseChainMapMatrix_self
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (i : Fin (N + 1)) :
    paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ i i le_rfl = 1 := by
  rw [paperEndpointFixedBaseChainMapMatrix, chainMap_self, LinearMap.toMatrix_id]

/-- In fixed basepoint bases, a one-edge segment is the corresponding fixed-base edge matrix. -/
theorem paperEndpointFixedBaseChainMapMatrix_edge
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) :
    paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ p.castSucc p.succ
        (Fin.castSucc_le_succ p) =
      paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p := by
  rw [paperEndpointFixedBaseChainMapMatrix, paperEndpointFixedBaseEdgeMatrix,
    chainMap_edge]

set_option linter.unusedDecidableInType false in
/-- Fixed-base variable chain-segment matrices compose by suffix times edge. -/
theorem paperEndpointFixedBaseChainMapMatrix_succ_right
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j) :
    paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ p.castSucc j
        ((Fin.castSucc_le_succ p).trans hpj) =
      paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ p.succ j hpj *
        paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p := by
  rw [paperEndpointFixedBaseChainMapMatrix, paperEndpointFixedBaseEdgeMatrix,
    chainMap_trans (reverseVertex W) (reverseEdge W C) p.castSucc
      (Fin.castSucc_le_succ p) hpj,
    chainMap_edge (reverseVertex W) (reverseEdge W C) p (Fin.castSucc_le_succ p)]
  exact LinearMap.toMatrix_comp
    (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ j)
    (chainMap (reverseVertex W) (reverseEdge W C) p.succ j hpj) (reverseEdge W C p)

/-- The fixed-base total matrix is the fixed-base matrix of the full reversed chain. -/
theorem paperEndpointFixedBaseTotalMatrix_eq_chainMapMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    paperEndpointFixedBaseTotalMatrix W B C U₀ hU₀ =
      paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀
        0 (Fin.last N) (Fin.zero_le (Fin.last N)) := by
  simp [paperEndpointFixedBaseTotalMatrix, paperEndpointFixedBaseChainMapMatrix,
    paperTotalMap, chainMap_reverse_eq_paper]

/-- At `C = B`, the fixed-base edge matrix is the endpoint adapted basepoint edge. -/
theorem paperEndpointFixedBaseEdgeMatrix_selfBase
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) :
    paperEndpointFixedBaseEdgeMatrix W B B U₀ hU₀ p =
      paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p :=
  rfl

/-- At `C = B`, the fixed-base total matrix is the endpoint adapted basepoint total. -/
theorem paperEndpointFixedBaseTotalMatrix_selfBase
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    paperEndpointFixedBaseTotalMatrix W B B U₀ hU₀ =
      paperEndpointAdaptedTotalMatrix W B U₀ hU₀ :=
  rfl

/-- A fixed-base variable edge has Schur-residual rank `ρ - r` under explicit chart and rank
hypotheses. -/
theorem rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_sub
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) {ρ : ℕ}
    (hdet : identityCornerDetChart (paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p))
    (hrank : (paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p).rank = ρ) :
    (schurResidualBlock (paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p)).rank =
      ρ - Module.finrank K U₀ := by
  let M := paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p
  have h := rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart M hdet
  rw [hrank] at h
  exact h

end FixedBase

section FixedBaseThreeLayer

universe u v

variable {K : Type u} [Field K]
  (W : Fin 3 → Type v) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  (B C : ∀ i : Fin 2, W i.succ →ₗ[K] W i.castSucc)

/-- In a two-edge paper chain, the first fixed-base edge matrix with canonical vertices. -/
abbrev paperEndpointFixedBaseTwoEdgeEdge0Matrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 1)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K :=
  paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ 0 1 (by decide)

/-- In a two-edge paper chain, the second fixed-base edge matrix with canonical vertices. -/
abbrev paperEndpointFixedBaseTwoEdgeEdge1Matrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last 2))
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 1) K :=
  paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ 1 (Fin.last 2) (by decide)

/-- In a two-edge paper chain, the total fixed-base matrix with canonical vertices. -/
abbrev paperEndpointFixedBaseTwoEdgeTotalMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last 2))
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K :=
  paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀
    0 (Fin.last 2) (Fin.zero_le (Fin.last 2))

/-- In a two-edge paper chain, the total fixed-base matrix is edge `1` times edge `0`. -/
theorem paperEndpointFixedBaseTwoEdgeTotalMatrix_eq_edge1_mul_edge0
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    paperEndpointFixedBaseTwoEdgeTotalMatrix W B C U₀ hU₀ =
      paperEndpointFixedBaseTwoEdgeEdge1Matrix W B C U₀ hU₀ *
        paperEndpointFixedBaseTwoEdgeEdge0Matrix W B C U₀ hU₀ := by
  rw [paperEndpointFixedBaseTwoEdgeTotalMatrix, paperEndpointFixedBaseTwoEdgeEdge1Matrix,
    paperEndpointFixedBaseTwoEdgeEdge0Matrix, paperEndpointFixedBaseChainMapMatrix]
  rw [chainMap_trans (reverseVertex W) (reverseEdge W C) 0
    (m := (1 : Fin 3)) (j := Fin.last 2) (by decide) (by decide)]
  exact LinearMap.toMatrix_comp
    (paperEndpointFixedBaseBasis W B U₀ hU₀ 0)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ 1)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ (Fin.last 2))
    (chainMap (reverseVertex W) (reverseEdge W C) 1 (Fin.last 2) (by decide))
    (chainMap (reverseVertex W) (reverseEdge W C) 0 1 (by decide))

end FixedBaseThreeLayer

section FixedBaseTopology

universe u v

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

/-- The determinant chart is a neighborhood of the base chain's fixed-base edge matrix. -/
theorem paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) :
    {M : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K |
      identityCornerDetChart M} ∈
      nhds (paperEndpointFixedBaseEdgeMatrix W B B U₀ hU₀ p) := by
  simpa [paperEndpointFixedBaseEdgeMatrix_selfBase] using
    paperEndpointAdaptedEdgeMatrix_mem_nhds_identityCornerDetChart W B U₀ hU₀ p

end FixedBaseTopology

end Aoyagi
end DLN
end DLNFibre
