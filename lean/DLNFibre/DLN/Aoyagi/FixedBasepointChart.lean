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

end Aoyagi
end DLN
end DLNFibre
