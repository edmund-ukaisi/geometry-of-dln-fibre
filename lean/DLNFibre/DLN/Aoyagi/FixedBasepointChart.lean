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

/-- A reversed variable chain segment expressed in the endpoint bases fixed from `B`. -/
def paperEndpointFixedBaseChainMapMatrixOfReverseEdges
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ i) K :=
  LinearMap.toMatrix
    (paperEndpointFixedBaseBasis W B U₀ hU₀ i)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ j)
    (chainMap (reverseVertex W) E i j hij)

/-- One reversed variable edge expressed in the endpoint bases fixed from `B`. -/
def paperEndpointFixedBaseEdgeMatrixOfReverseEdges
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
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
    (E p)

/-- A reversed edge family whose fixed-base edge matrices are prescribed. -/
def paperEndpointFixedBaseReverseEdgeFamilyOfMatrices
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (M : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K) :
    ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
  fun p ↦
    Matrix.toLin
      (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
      (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
      (M p)

set_option linter.unusedSectionVars false in
/-- Prescribed fixed-base edge matrices are recovered from the realised
reversed edge family. -/
theorem paperEndpointFixedBaseEdgeMatrixOfReverseEdges_reverseEdgeFamilyOfMatrices
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (M : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K)
    (p : Fin N) :
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (paperEndpointFixedBaseReverseEdgeFamilyOfMatrices W B U₀ hU₀ M) p =
      M p := by
  simp [paperEndpointFixedBaseEdgeMatrixOfReverseEdges,
    paperEndpointFixedBaseReverseEdgeFamilyOfMatrices]

/-- The reversed variable total product expressed in the endpoint bases fixed from `B`. -/
def paperEndpointFixedBaseTotalMatrixOfReverseEdges
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K :=
  LinearMap.toMatrix
    (paperEndpointFixedBaseBasis W B U₀ hU₀ 0)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ (Fin.last N))
    (chainMap (reverseVertex W) E 0 (Fin.last N) (Fin.zero_le (Fin.last N)))

set_option linter.unusedDecidableInType false in
/-- In fixed basepoint bases, an empty variable chain segment has identity matrix. -/
theorem paperEndpointFixedBaseChainMapMatrix_self
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (i : Fin (N + 1)) :
    paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ i i le_rfl = 1 := by
  rw [paperEndpointFixedBaseChainMapMatrix, chainMap_self, LinearMap.toMatrix_id]

/-- Fixed-base variable chain-segment matrices are independent of the order proof. -/
theorem paperEndpointFixedBaseChainMapMatrix_proof_irrel
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (i j : Fin (N + 1)) (hij hij' : i ≤ j) :
    paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ i j hij =
      paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ i j hij' := by
  congr

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

set_option linter.unusedDecidableInType false in
/-- In fixed basepoint bases, an empty reversed variable segment has identity matrix. -/
theorem paperEndpointFixedBaseChainMapMatrixOfReverseEdges_self
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    (i : Fin (N + 1)) :
    paperEndpointFixedBaseChainMapMatrixOfReverseEdges W B U₀ hU₀ E i i le_rfl = 1 := by
  rw [paperEndpointFixedBaseChainMapMatrixOfReverseEdges, chainMap_self, LinearMap.toMatrix_id]

/-- Fixed-base reversed variable chain-segment matrices are independent of the order proof. -/
theorem paperEndpointFixedBaseChainMapMatrixOfReverseEdges_proof_irrel
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    (i j : Fin (N + 1)) (hij hij' : i ≤ j) :
    paperEndpointFixedBaseChainMapMatrixOfReverseEdges W B U₀ hU₀ E i j hij =
      paperEndpointFixedBaseChainMapMatrixOfReverseEdges W B U₀ hU₀ E i j hij' := by
  congr

/-- In fixed basepoint bases, a one-edge reversed segment is the corresponding edge matrix. -/
theorem paperEndpointFixedBaseChainMapMatrixOfReverseEdges_edge
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    (p : Fin N) :
    paperEndpointFixedBaseChainMapMatrixOfReverseEdges W B U₀ hU₀ E p.castSucc p.succ
        (Fin.castSucc_le_succ p) =
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E p := by
  rw [paperEndpointFixedBaseChainMapMatrixOfReverseEdges,
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges, chainMap_edge]

set_option linter.unusedDecidableInType false in
/-- Fixed-base reversed variable chain-segment matrices compose by suffix times edge. -/
theorem paperEndpointFixedBaseChainMapMatrixOfReverseEdges_succ_right
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j) :
    paperEndpointFixedBaseChainMapMatrixOfReverseEdges W B U₀ hU₀ E p.castSucc j
        ((Fin.castSucc_le_succ p).trans hpj) =
      paperEndpointFixedBaseChainMapMatrixOfReverseEdges W B U₀ hU₀ E p.succ j hpj *
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E p := by
  rw [paperEndpointFixedBaseChainMapMatrixOfReverseEdges,
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges,
    chainMap_trans (reverseVertex W) E p.castSucc (Fin.castSucc_le_succ p) hpj,
    chainMap_edge (reverseVertex W) E p (Fin.castSucc_le_succ p)]
  exact LinearMap.toMatrix_comp
    (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
    (paperEndpointFixedBaseBasis W B U₀ hU₀ j)
    (chainMap (reverseVertex W) E p.succ j hpj) (E p)

/-- The fixed-base reversed total matrix is the matrix of the full reversed chain. -/
theorem paperEndpointFixedBaseTotalMatrixOfReverseEdges_eq_chainMapMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ) :
    paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E =
      paperEndpointFixedBaseChainMapMatrixOfReverseEdges W B U₀ hU₀ E
        0 (Fin.last N) (Fin.zero_le (Fin.last N)) := by
  rfl

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

/-- A fixed-base variable edge matrix has the rank of the underlying variable edge map. -/
theorem rank_paperEndpointFixedBaseEdgeMatrix_eq_finrank_range
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) :
    (paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p).rank =
      Module.finrank K (LinearMap.range (reverseEdge W C p)) := by
  dsimp [paperEndpointFixedBaseEdgeMatrix]
  exact rank_toMatrix_eq_finrank_range _ _ (reverseEdge W C p)

/-- A fixed-base reversed-edge matrix has the rank of the underlying edge map. -/
theorem rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    (p : Fin N) :
    (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E p).rank =
      Module.finrank K (LinearMap.range (E p)) := by
  dsimp [paperEndpointFixedBaseEdgeMatrixOfReverseEdges]
  exact rank_toMatrix_eq_finrank_range _ _ (E p)

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

/-- A fixed-base variable edge has Schur-residual rank equal to source rank minus through-rank. -/
theorem rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_range_sub
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N)
    (hdet : identityCornerDetChart (paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p)) :
    (schurResidualBlock (paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p)).rank =
      Module.finrank K (LinearMap.range (reverseEdge W C p)) - Module.finrank K U₀ := by
  exact rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_sub W B C U₀ hU₀ p
    hdet (rank_paperEndpointFixedBaseEdgeMatrix_eq_finrank_range W B C U₀ hU₀ p)

/-- A transformed fixed-base reversed edge has Schur-residual rank `ρ - r` under
explicit chart and rank hypotheses on the untransformed edge. -/
theorem rank_schurResidualBlock_transformed_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_sub
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    (p : Fin N)
    (Bprev : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K)
    {ρ : ℕ}
    (hdet : identityCornerDetChart
      (fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        Bprev 0
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          K) *
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E p))
    (hrank : (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E p).rank = ρ) :
    (schurResidualBlock
      (fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        Bprev 0
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          K) *
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E p)).rank =
      ρ - Module.finrank K U₀ := by
  let A : Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
      K :=
    fromBlocks
      (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
      Bprev 0
      (1 : Matrix
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K)
  let M := A * paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E p
  have hA : IsUnit A.det := by
    exact (Matrix.isUnit_iff_isUnit_det (A := A)).mp
      ((Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩)
  have hMrank : M.rank = ρ := by
    simp [M, A, hrank,
      Matrix.rank_mul_eq_right_of_isUnit_det A
        (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E p) hA]
  have h := rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart M hdet
  rw [hMrank] at h
  exact h

/-- A transformed fixed-base reversed edge has Schur-residual rank equal to source
rank minus through-rank. -/
theorem
    rank_schurResidualBlock_transformed_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_range_sub
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    (p : Fin N)
    (Bprev : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K)
    (hdet : identityCornerDetChart
      (fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        Bprev 0
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          K) *
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E p)) :
    (schurResidualBlock
      (fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        Bprev 0
        (1 : Matrix
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          K) *
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E p)).rank =
      Module.finrank K (LinearMap.range (E p)) - Module.finrank K U₀ := by
  exact
    rank_schurResidualBlock_transformed_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_sub
      W B U₀ hU₀ E p Bprev hdet
      (rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range W B U₀ hU₀ E p)

/-- A deterministic transformed fixed-base reversed edge has Schur-residual rank equal to
source rank minus through-rank. -/
theorem
    rank_transformedEdge_fixedBaseReverseEdges_eq_range_sub
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀) K
      j p.succ)
    (hdet : identityCornerDetChart
      (ChartLocalSuffixState.transformedEdge
        (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E) p S)) :
    (schurResidualBlock
      (ChartLocalSuffixState.transformedEdge
        (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E) p S)).rank =
      Module.finrank K (LinearMap.range (E p)) - Module.finrank K U₀ := by
  simpa [ChartLocalSuffixState.transformedEdge] using
    rank_schurResidualBlock_transformed_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_range_sub
      W B U₀ hU₀ E p S.B hdet

/-- One fixed-base chart-local suffix step with a supplied transformed variable edge. -/
theorem paperEndpointFixedBase_chartLocal_suffixStep
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j)
    (M : Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K)
    (Lprev : Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j) K)
    (Rprev : Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K)
    (Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (Dprev : Matrix
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K)
    (hPtail : Lprev * paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ p.succ j hpj *
        Rprev = fromBlocks Ctop 0 0 Dprev)
    (hEdge : paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p = Rprev * M)
    (hCtop : IsUnit Ctop.det) (hM : identityCornerDetChart M) :
    let Lstep : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j) K :=
      fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) 0
        (-(Dprev * lowerLeftBlock M * (Ctop * topLeftCorner M)⁻¹)) 1
    let Rstep : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        (-((topLeftCorner M)⁻¹ * upperRightBlock M)) 0 1
    Lstep * Lprev *
        paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ p.castSucc j
          ((Fin.castSucc_le_succ p).trans hpj) *
        Rstep =
      fromBlocks (Ctop * topLeftCorner M) 0 0 (Dprev * schurResidualBlock M) := by
  dsimp
  rw [paperEndpointFixedBaseChainMapMatrix_succ_right W B C U₀ hU₀ p j hpj]
  exact productReduction_chartLocal_suffixStep_fromBlocks_indexed
    (paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ p.succ j hpj)
    (paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p) M Lprev Rprev Ctop Dprev
    hPtail hEdge hCtop hM

/-- Fixed-base chart-local suffix-chain block diagonalisation under explicit chart hypotheses. -/
theorem productReduction_paperEndpointFixedBaseChainMapMatrix_chartLocal_blockDiagonal
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (hchart : ∀ (p : Fin N)
      (Bprev : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K),
      identityCornerDetChart
        (fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          Bprev 0
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) *
          paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀ p))
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    ∃ L : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j) K,
      ∃ Bmat : Matrix (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ i) K,
        ∃ Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K,
          ∃ D : Matrix
              (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
              (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ i)
              K,
            IsUnit L.det ∧ IsUnit Ctop.det ∧
              L * paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀ i j hij *
                  fromBlocks
                    (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                    (-Bmat) 0
                    (1 : Matrix
                      (throughSubspaceEndpointComplementIndex
                        (reverseVertex W) (reverseEdge W B) U₀ i)
                      (throughSubspaceEndpointComplementIndex
                        (reverseVertex W) (reverseEdge W B) U₀ i) K) =
                fromBlocks Ctop 0 0 D := by
  exact productReduction_chartLocal_suffixChain_blockDiagonal_indexed
    (E := paperEndpointFixedBaseEdgeMatrix W B C U₀ hU₀)
    (P := paperEndpointFixedBaseChainMapMatrix W B C U₀ hU₀)
    (hPproof := fun {i j} h h' ↦
      paperEndpointFixedBaseChainMapMatrix_proof_irrel W B C U₀ hU₀ i j h h')
    (hself := paperEndpointFixedBaseChainMapMatrix_self W B C U₀ hU₀)
    (hsuccRight := paperEndpointFixedBaseChainMapMatrix_succ_right W B C U₀ hU₀)
    (hchart := hchart) i j hij

/-- Endpoint fixed-base block diagonalisation from the recursive determinant charts actually
visited by the deterministic suffix-state construction. -/
theorem paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    (hchart : ∀ p : Fin N,
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
          p
          (ChartLocalSuffixState.suffixState
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
            (Fin.last N) p.succ p.succ.le_last))) :
    let S := ChartLocalSuffixState.suffixState
      (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
      (Fin.last N) 0 (Fin.zero_le (Fin.last N))
    IsUnit S.L.det ∧ IsUnit S.Ctop.det ∧
      S.L * paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E *
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            (-S.B) 0
            (1 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
        fromBlocks S.Ctop 0 0 S.D := by
  let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
  let P := paperEndpointFixedBaseChainMapMatrixOfReverseEdges W B U₀ hU₀ E
  let S := ChartLocalSuffixState.suffixState EMat
    (Fin.last N) 0 (Fin.zero_le (Fin.last N))
  have hS : S.BlockDiagonal P (Fin.zero_le (Fin.last N)) := by
    dsimp [S]
    exact ChartLocalSuffixState.suffixState_blockDiagonal EMat P
      (fun {i j} h h' ↦
        paperEndpointFixedBaseChainMapMatrixOfReverseEdges_proof_irrel
          W B U₀ hU₀ E i j h h')
      (paperEndpointFixedBaseChainMapMatrixOfReverseEdges_self W B U₀ hU₀ E)
      (paperEndpointFixedBaseChainMapMatrixOfReverseEdges_succ_right W B U₀ hU₀ E)
      (i := 0) (j := Fin.last N) (Fin.zero_le (Fin.last N))
      (fun p hpj ↦ by
        have hstate :
            ChartLocalSuffixState.suffixState EMat (Fin.last N) p.succ hpj =
              ChartLocalSuffixState.suffixState EMat (Fin.last N) p.succ
                p.succ.le_last := by
          congr
        simpa [EMat, hstate] using hchart p)
  simpa [ChartLocalSuffixState.BlockDiagonal, S, P,
    paperEndpointFixedBaseTotalMatrixOfReverseEdges_eq_chainMapMatrix] using hS

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

/-- At the fixed base chain, each transformed fixed-base edge determinant chart is a
neighborhood of the untransformed edge matrix. -/
theorem paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_transformed_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N)
    (Bprev : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K) :
    {M : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K |
      identityCornerDetChart
        (fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          Bprev 0
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) * M)} ∈
      nhds (paperEndpointFixedBaseEdgeMatrix W B B U₀ hU₀ p) := by
  have hdet :
      identityCornerDetChart
        (fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          Bprev 0
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) *
            paperEndpointFixedBaseEdgeMatrix W B B U₀ hU₀ p) := by
    convert
      (identityCornerDetChart_unitriangular_paperEndpointAdaptedEdgeMatrix
        W B U₀ hU₀ p (-Bprev)) using 2
    rw [paperEndpointUnitriangularLeft]
    congr
    exact (neg_neg Bprev).symm
  exact fromBlocks_leftMul_identityCornerDetChart_mem_nhds Bprev hdet

end FixedBaseTopology

section FixedBaseContinuousEdgeTopology

universe u v

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)] [∀ i, T2Space (W i)]
  [∀ i, Module K (W i)] [∀ i, ContinuousSMul K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

/-- A continuous reversed edge family whose fixed-base edge matrices are prescribed. -/
def paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (M : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K) :
    ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ :=
  fun p ↦
    LinearMap.toContinuousLinearMap
      (paperEndpointFixedBaseReverseEdgeFamilyOfMatrices W B U₀ hU₀ M p)

set_option linter.unusedSectionVars false in
/-- Prescribed fixed-base edge matrices are recovered from the realised
continuous reversed edge family. -/
theorem paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (M : ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K)
    (p : Fin N) :
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
        (fun q ↦
          (paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices W B U₀ hU₀ M q :
            reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ)) p =
      M p := by
  simpa [paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices] using
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges_reverseEdgeFamilyOfMatrices
      (K := K) W B U₀ hU₀ M p

/-- Realising prescribed fixed-base edge matrices as continuous reversed edges is continuous
in the prescribed matrices. -/
theorem paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuous
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    Continuous
      (fun M : ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K ↦
        paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices W B U₀ hU₀ M) := by
  classical
  refine continuous_pi ?_
  intro p
  have hrealise : Continuous
      (fun M :
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K ↦
        LinearMap.toContinuousLinearMap
          (Matrix.toLin
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ) M)) :=
    continuous_matrix_toContinuousLinearMap
      (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
      (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
  simpa [paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices,
    paperEndpointFixedBaseReverseEdgeFamilyOfMatrices] using hrealise.comp (continuous_apply p)

/-- Continuous-at version of
`paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuous`. -/
theorem paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (M : α → ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K)
    (hM : ContinuousAt M x₀) :
    ContinuousAt
      (fun x : α ↦
        paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices W B U₀ hU₀ (M x)) x₀ :=
  (paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuous
    (K := K) W B U₀ hU₀).continuousAt.comp hM

/-- Fixed-base edge matrix coordinates vary continuously with a continuous
reversed edge family. -/
theorem paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : ContinuousAt Cedge x₀) :
    ContinuousAt
      (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))) x₀ := by
  refine continuousAt_pi.2 ?_
  intro p
  have hCedge_p : ContinuousAt (fun x : α ↦ Cedge x p) x₀ :=
    (continuous_apply p).continuousAt.comp hCedge
  have hcoord : Continuous
      (fun f : reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (f : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) :=
    continuous_linearMap_toMatrix
      (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
      (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
  simpa [paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using
    hcoord.continuousAt.comp hCedge_p

/-- For a single fixed-base edge parameter, the transformed determinant chart pulls back to a
neighborhood of the base edge in the continuous-linear-map topology. -/
theorem paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N)
    (Bprev : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K) :
    {f : reverseVertex W p.castSucc →L[K] reverseVertex W p.succ |
      identityCornerDetChart
        (fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          Bprev 0
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) *
          LinearMap.toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
            (f : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))} ∈
      nhds (LinearMap.toContinuousLinearMap (reverseEdge W B p)) := by
  let coord :
      (reverseVertex W p.castSucc →L[K] reverseVertex W p.succ) →
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun f ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (f : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  have hcoord : Continuous coord :=
    continuous_linearMap_toMatrix
      (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
      (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
  have hmat :
      {M : Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K |
        identityCornerDetChart
          (fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            Bprev 0
            (1 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ p.succ)
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) * M)} ∈
        nhds (coord (LinearMap.toContinuousLinearMap (reverseEdge W B p))) := by
    simpa [coord, paperEndpointFixedBaseEdgeMatrix] using
      paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_transformed_identityCornerDetChart
        W B U₀ hU₀ p Bprev
  exact hcoord.continuousAt.preimage_mem_nhds hmat

/-- For a fixed family of accumulated upper blocks, all transformed determinant charts
hold on a neighborhood of the base edge family in the product topology. -/
theorem paperEndpointFixedBaseContinuousEdges_selfBase_mem_nhds_transformed_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Bprev : ∀ p : Fin N, Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K) :
    {Cedge : ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ |
      ∀ p : Fin N,
        identityCornerDetChart
          (fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            (Bprev p) 0
            (1 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ p.succ)
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) *
            LinearMap.toMatrix
              (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
              (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
              (Cedge p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))} ∈
      nhds (fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) := by
  classical
  simpa [Set.setOf_forall] using
    (Filter.iInter_mem.2 fun p ↦
      (continuous_apply p).continuousAt.preimage_mem_nhds
        (paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart
          W B U₀ hU₀ p (Bprev p)))

/-- If edge parameters and accumulated upper blocks vary continuously, transformed
determinant charts persist in a neighborhood of the parameter. -/
theorem
    paperEndpointFixedBaseContinuousEdges_variableBprev_mem_nhds_transformed_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (Bprev : α → ∀ p : Fin N, Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K)
    (hCedge : ContinuousAt Cedge x₀)
    (hBprev : ContinuousAt Bprev x₀)
    (hchart₀ : ∀ p : Fin N,
      identityCornerDetChart
        (fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (Bprev x₀ p) 0
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) *
          LinearMap.toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
            (Cedge x₀ p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))) :
    {x : α |
      ∀ p : Fin N,
        identityCornerDetChart
          (fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            (Bprev x p) 0
            (1 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ p.succ)
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) *
            LinearMap.toMatrix
              (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
              (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
              (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ))} ∈
      nhds x₀ := by
  classical
  simpa [Set.setOf_forall] using
    (Filter.iInter_mem.2 fun p : Fin N ↦ by
      have hBprev_p : ContinuousAt (fun x : α ↦ Bprev x p) x₀ :=
        (continuous_apply p).continuousAt.comp hBprev
      have hleft : ContinuousAt
          (fun x : α ↦
            fromBlocks
              (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
              (Bprev x p) 0
              (1 : Matrix
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ p.succ)
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ p.succ) K)) x₀ := by
        have hfrom : Continuous
            (fun F : Matrix (Fin (Module.finrank K U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ p.succ) K ↦
              fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                F 0
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ p.succ)
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ p.succ) K)) :=
          continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const
        exact hfrom.continuousAt.comp hBprev_p
      have hCedge_p : ContinuousAt (fun x : α ↦ Cedge x p) x₀ :=
        (continuous_apply p).continuousAt.comp hCedge
      have hcoord : ContinuousAt
          (fun x : α ↦
            LinearMap.toMatrix
              (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
              (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
              (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) x₀ := by
        have hcoord' : Continuous
            (fun f : reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦
              LinearMap.toMatrix
                (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
                (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
                (f : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) :=
          continuous_linearMap_toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        exact hcoord'.continuousAt.comp hCedge_p
      have hmul : ContinuousAt
          (fun x : α ↦
            fromBlocks
              (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
              (Bprev x p) 0
              (1 : Matrix
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ p.succ)
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) *
            LinearMap.toMatrix
              (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
              (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
              (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) x₀ := by
        have hmul' : Continuous (fun q :
            Matrix
              (Fin (Module.finrank K U₀) ⊕
                throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ p.succ)
              (Fin (Module.finrank K U₀) ⊕
                throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ p.succ) K ×
            Matrix
              (Fin (Module.finrank K U₀) ⊕
                throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ p.succ)
              (Fin (Module.finrank K U₀) ⊕
                throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K ↦
            q.1 * q.2) :=
          continuous_fst.matrix_mul continuous_snd
        exact hmul'.continuousAt.comp (hleft.prodMk hcoord)
      exact hmul.preimage_mem_nhds (identityCornerDetChart_mem_nhds (hchart₀ p)))

/-- For the recursively produced accumulated upper blocks, transformed determinant charts
persist in a neighborhood of the parameter. -/
theorem
    paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : ContinuousAt Cedge x₀)
    (hchart₀ : ∀ p : Fin N,
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (fun q : Fin N ↦
            LinearMap.toMatrix
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
              (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
          p
          (ChartLocalSuffixState.suffixState
            (fun q : Fin N ↦
              LinearMap.toMatrix
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
            (Fin.last N) p.succ p.succ.le_last))) :
    {x : α |
      ∀ p : Fin N,
        identityCornerDetChart
          (ChartLocalSuffixState.transformedEdge
            (fun q : Fin N ↦
              LinearMap.toMatrix
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                (Cedge x q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
            p
            (ChartLocalSuffixState.suffixState
              (fun q : Fin N ↦
                LinearMap.toMatrix
                  (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                  (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                  (Cedge x q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
              (Fin.last N) p.succ p.succ.le_last))} ∈
      nhds x₀ := by
  classical
  let E : α → ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun x p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let Bprev : α → ∀ p : Fin N, Matrix (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K :=
    fun x p ↦ (ChartLocalSuffixState.suffixState (E x) (Fin.last N)
      p.succ p.succ.le_last).B
  have hE : ContinuousAt E x₀ := by
    refine continuousAt_pi.2 ?_
    intro p
    have hCedge_p : ContinuousAt (fun x : α ↦ Cedge x p) x₀ :=
      (continuous_apply p).continuousAt.comp hCedge
    have hcoord : Continuous
        (fun f : reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦
          LinearMap.toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
            (f : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) :=
      continuous_linearMap_toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
    simpa [E] using hcoord.continuousAt.comp hCedge_p
  have hchartE : ∀ (p : Fin N) (hpj : p.succ ≤ Fin.last N),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge (E x₀) p
          (ChartLocalSuffixState.suffixState (E x₀) (Fin.last N) p.succ hpj)) := by
    intro p hpj
    simpa [E] using hchart₀ p
  have hBprev : ContinuousAt Bprev x₀ := by
    refine continuousAt_pi.2 ?_
    intro p
    simpa [Bprev] using
      continuousAt_chartLocalSuffixState_suffixState_B E hE hchartE p.succ p.succ.le_last
  have hnhds :=
    paperEndpointFixedBaseContinuousEdges_variableBprev_mem_nhds_transformed_identityCornerDetChart
      W B U₀ hU₀ Cedge Bprev hCedge hBprev (by
        intro p
        simpa [E, Bprev, ChartLocalSuffixState.transformedEdge] using hchart₀ p)
  simpa [E, Bprev, ChartLocalSuffixState.transformedEdge] using hnhds

/-- In endpoint bases fixed from `B`, the deterministic suffix-state fields vary
continuously with a continuous reversed-edge family. -/
theorem paperEndpointFixedBaseContinuousEdges_recursiveSuffixState_fields_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : ContinuousAt Cedge x₀)
    (hchart₀ : ∀ p : Fin N,
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (fun q : Fin N ↦
            LinearMap.toMatrix
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
              (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
          p
          (ChartLocalSuffixState.suffixState
            (fun q : Fin N ↦
              LinearMap.toMatrix
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
            (Fin.last N) p.succ p.succ.le_last))) :
    let E : α → ∀ p : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
      fun x p ↦
        LinearMap.toMatrix
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
          (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
          (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    ∀ i : Fin (N + 1), ∀ hi : i ≤ Fin.last N,
      IsUnit ((ChartLocalSuffixState.suffixState (E x₀) (Fin.last N) i hi).Ctop.det) ∧
        ContinuousAt
          (fun x : α ↦ (ChartLocalSuffixState.suffixState (E x) (Fin.last N) i hi).L) x₀ ∧
        ContinuousAt
          (fun x : α ↦ (ChartLocalSuffixState.suffixState (E x) (Fin.last N) i hi).B) x₀ ∧
        ContinuousAt
          (fun x : α ↦ (ChartLocalSuffixState.suffixState (E x) (Fin.last N) i hi).Ctop) x₀ ∧
        ContinuousAt
          (fun x : α ↦ (ChartLocalSuffixState.suffixState (E x) (Fin.last N) i hi).D) x₀ := by
  classical
  let E : α → ∀ p : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K :=
    fun x p ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
        (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  have hE : ContinuousAt E x₀ := by
    refine continuousAt_pi.2 ?_
    intro p
    have hCedge_p : ContinuousAt (fun x : α ↦ Cedge x p) x₀ :=
      (continuous_apply p).continuousAt.comp hCedge
    have hcoord : Continuous
        (fun f : reverseVertex W p.castSucc →L[K] reverseVertex W p.succ ↦
          LinearMap.toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
            (f : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)) :=
      continuous_linearMap_toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ p.succ)
    simpa [E] using hcoord.continuousAt.comp hCedge_p
  have hchartE : ∀ (p : Fin N) (hpj : p.succ ≤ Fin.last N),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge (E x₀) p
          (ChartLocalSuffixState.suffixState (E x₀) (Fin.last N) p.succ hpj)) := by
    intro p hpj
    simpa [E] using hchart₀ p
  simpa [E] using
    continuousAt_chartLocalSuffixState_suffixState_fields E hE hchartE

/-- In endpoint bases fixed from `B`, the transformed Schur residual blocks
visited by the suffix recursion vary continuously with a continuous reversed
edge family, assuming the basepoint recursive determinant charts. -/
theorem paperEndpointFixedBaseContinuousEdges_residualBlock_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : ContinuousAt Cedge x₀)
    (hchart₀ : ∀ p : Fin N,
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (fun q : Fin N ↦
            LinearMap.toMatrix
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
              (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
          p
          (ChartLocalSuffixState.suffixState
            (fun q : Fin N ↦
              LinearMap.toMatrix
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
            (Fin.last N) p.succ p.succ.le_last)))
    (p : Fin N) :
    let E : α → ∀ q : Fin N,
        Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ q.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ q.castSucc) K :=
      fun x ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun q : Fin N ↦
            (Cedge x q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
    ContinuousAt
      (fun x : α ↦
        ChartLocalSuffixState.residualBlock (E x) (Fin.last N) p p.succ.le_last) x₀ := by
  intro E
  have hE : ContinuousAt E x₀ := by
    simpa [E] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousAt
        (K := K) W B U₀ hU₀ Cedge hCedge
  have hchartE : ∀ (q : Fin N) (hq : q.succ ≤ Fin.last N),
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge (E x₀) q
          (ChartLocalSuffixState.suffixState (E x₀) (Fin.last N) q.succ hq)) := by
    intro q hq
    simpa [E] using hchart₀ q
  exact
    continuousAt_chartLocalSuffixState_residualBlock
      (K := K) E hE hchartE p p.succ.le_last

/-- If the base parameter is the fixed paper chain `B`, the recursive transformed determinant
charts required by the suffix-state topology handoff hold automatically. -/
theorem
    paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_detChart
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    ∀ p : Fin N,
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (fun q : Fin N ↦
            LinearMap.toMatrix
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
              (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
          p
          (ChartLocalSuffixState.suffixState
            (fun q : Fin N ↦
              LinearMap.toMatrix
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
            (Fin.last N) p.succ p.succ.le_last)) := by
  intro p
  let EMat : ∀ q : Fin N,
      Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ q.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ q.castSucc) K :=
    fun q ↦
      LinearMap.toMatrix
        (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
        (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
        (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ)
  let S := ChartLocalSuffixState.suffixState EMat (Fin.last N) p.succ p.succ.le_last
  have hunit :
      identityCornerDetChart
        (fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          S.B 0
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ)
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) *
          paperEndpointFixedBaseEdgeMatrix W B B U₀ hU₀ p) := by
    have hunit' :=
      identityCornerDetChart_unitriangular_paperEndpointAdaptedEdgeMatrix
        W B U₀ hU₀ p (-S.B)
    have hunit'' :
        identityCornerDetChart
          (fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            (-(-S.B)) 0
            (1 : Matrix
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ p.succ)
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) *
            paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p) := by
      simpa [paperEndpointUnitriangularLeft] using hunit'
    convert hunit'' using 2
    rw [show - -S.B = S.B by
      ext a b
      simp]
  simpa [EMat, S, ChartLocalSuffixState.transformedEdge, hbase,
    paperEndpointFixedBaseEdgeMatrix] using hunit

/-- The recursive transformed determinant-chart predicates for a continuous reversed-edge
family in endpoint bases fixed from `B`. -/
def paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) : Prop :=
  ∀ p : Fin N,
    identityCornerDetChart
      (ChartLocalSuffixState.transformedEdge
        (fun q : Fin N ↦
          LinearMap.toMatrix
            (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
            (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
            (Cedge x q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
        p
        (ChartLocalSuffixState.suffixState
          (fun q : Fin N ↦
            LinearMap.toMatrix
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
              (Cedge x q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
          (Fin.last N) p.succ p.succ.le_last))

/-- The deterministic endpoint block form for a continuous reversed edge family in the
endpoint bases fixed from `B`. -/
def paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (x : α) : Prop :=
  let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let S := ChartLocalSuffixState.suffixState
    (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
    (Fin.last N) 0 (Fin.zero_le (Fin.last N))
  IsUnit S.L.det ∧ IsUnit S.Ctop.det ∧
    S.L * paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E *
        fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (-S.B) 0
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
      fromBlocks S.Ctop 0 0 S.D

/-- Pointwise residual-rank consequences available once exact edge ranks are supplied. -/
def paperEndpointFixedBaseContinuousEdgesRecursiveResidualRankImplications
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ) (x : α) : Prop :=
  let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  ∀ p : Fin N,
    Module.finrank K (LinearMap.range (E p)) = rEdge p →
      (ChartLocalSuffixState.residualBlock
        (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
        (Fin.last N) p p.succ.le_last).rank =
        rEdge p - Module.finrank K U₀

/-- Near a parameter where the recursive transformed determinant charts hold, the fixed-base
endpoint product has the deterministic block diagonal form. -/
theorem paperEndpointFixedBaseContinuousEdges_recursiveBprev_blockDiagonal_mem_nhds
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : ContinuousAt Cedge x₀)
    (hchart₀ : ∀ p : Fin N,
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (fun q : Fin N ↦
            LinearMap.toMatrix
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
              (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
              (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
          p
          (ChartLocalSuffixState.suffixState
            (fun q : Fin N ↦
              LinearMap.toMatrix
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                (Cedge x₀ q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
            (Fin.last N) p.succ p.succ.le_last))) :
    {x : α |
      paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal W B U₀ hU₀ Cedge x} ∈
      nhds x₀ := by
  classical
  have hcharts :
      {x : α |
        ∀ p : Fin N,
          identityCornerDetChart
            (ChartLocalSuffixState.transformedEdge
              (fun q : Fin N ↦
                LinearMap.toMatrix
                  (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                  (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                  (Cedge x q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
              p
              (ChartLocalSuffixState.suffixState
                (fun q : Fin N ↦
                  LinearMap.toMatrix
                    (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                    (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                    (Cedge x q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
                (Fin.last N) p.succ p.succ.le_last))} ∈
        nhds x₀ :=
    paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart
      W B U₀ hU₀ Cedge hCedge hchart₀
  exact Filter.mem_of_superset hcharts (by
    intro x hx
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    have hxE : ∀ p : Fin N,
        identityCornerDetChart
          (ChartLocalSuffixState.transformedEdge
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
            p
            (ChartLocalSuffixState.suffixState
              (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
              (Fin.last N) p.succ p.succ.le_last)) := by
      intro p
      simpa [E, paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using hx p
    simpa [paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal, E] using
      paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal
        W B U₀ hU₀ E hxE)

/-- Near a continuous edge family based at the fixed paper chain `B`, the fixed-base
endpoint product has the deterministic block diagonal form. -/
theorem paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_mem_nhds
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    {x : α |
      paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal W B U₀ hU₀ Cedge x} ∈
      nhds x₀ :=
  paperEndpointFixedBaseContinuousEdges_recursiveBprev_blockDiagonal_mem_nhds
    W B U₀ hU₀ Cedge hCedge
    (paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_detChart
      W B U₀ hU₀ Cedge hbase)

/-- Near a continuous edge family based at `B`, the recursive charts, endpoint block form,
and pointwise residual-rank implications all hold. -/
theorem
    paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_rankImp_mem_nhds
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    {x : α |
      paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts W B U₀ hU₀ Cedge x ∧
      paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal W B U₀ hU₀ Cedge x ∧
      paperEndpointFixedBaseContinuousEdgesRecursiveResidualRankImplications
        W B U₀ hU₀ Cedge rEdge x} ∈
      nhds x₀ := by
  classical
  have hchart₀ :=
    paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_detChart
      W B U₀ hU₀ Cedge hbase
  have hraw :
      {x : α |
        ∀ p : Fin N,
          identityCornerDetChart
            (ChartLocalSuffixState.transformedEdge
              (fun q : Fin N ↦
                LinearMap.toMatrix
                  (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                  (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                  (Cedge x q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
              p
              (ChartLocalSuffixState.suffixState
                (fun q : Fin N ↦
                  LinearMap.toMatrix
                    (paperEndpointFixedBaseBasis W B U₀ hU₀ q.castSucc)
                    (paperEndpointFixedBaseBasis W B U₀ hU₀ q.succ)
                    (Cedge x q : reverseVertex W q.castSucc →ₗ[K] reverseVertex W q.succ))
                (Fin.last N) p.succ p.succ.le_last))} ∈
        nhds x₀ :=
    paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart
      W B U₀ hU₀ Cedge hCedge hchart₀
  have hcharts :
      {x : α |
        paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts W B U₀ hU₀ Cedge x} ∈
      nhds x₀ := by
    simpa [paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts] using
      hraw
  exact Filter.mem_of_superset hcharts (by
    intro x hx
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    have hxE : ∀ p : Fin N,
        identityCornerDetChart
          (ChartLocalSuffixState.transformedEdge
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
            p
            (ChartLocalSuffixState.suffixState
              (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
              (Fin.last N) p.succ p.succ.le_last)) := by
      intro p
      simpa [paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts, E,
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using hx p
    refine ⟨hx, ?_, ?_⟩
    · simpa [paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal, E] using
        paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal
          W B U₀ hU₀ E hxE
    · intro p hrank
      have hres :=
        rank_transformedEdge_fixedBaseReverseEdges_eq_range_sub
          W B U₀ hU₀ E p
          (ChartLocalSuffixState.suffixState
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E)
            (Fin.last N) p.succ p.succ.le_last)
          (hxE p)
      simpa [paperEndpointFixedBaseContinuousEdgesRecursiveResidualRankImplications,
        ChartLocalSuffixState.residualBlock, E, hrank] using hres)

end FixedBaseContinuousEdgeTopology

end Aoyagi
end DLN
end DLNFibre
