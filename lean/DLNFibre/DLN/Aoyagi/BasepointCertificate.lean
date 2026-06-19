import DLNFibre.DLN.Aoyagi.ChartTopology

/-!
# Basepoint endpoint certificates for Aoyagi product reduction

This file packages the pointwise adapted-coordinate facts available at a fixed
Aoyagi-order chain.  The certificate is deliberately basepoint-only: it does
not assert a fixed-coordinate neighborhood theorem for variable chains, rank
stratum openness, or RLCT consequences.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

section EndpointRank

variable {K : Type*} [Field K] {N : ℕ}
  (V : Fin (N + 1) → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  (A : ∀ i : Fin N, V i.castSucc →ₗ[K] V i.succ)

set_option linter.unusedDecidableInType false in
/-- The residual block of an endpoint-adapted edge has source rank minus the through-rank. -/
theorem lowerRightBlock_throughSubspaceEndpointAdaptedEdgeMatrix_rank_eq_sub
    [∀ j, FiniteDimensional K (V j)]
    (U₀ : Submodule K (V 0))
    (hU₀ : IsCompl U₀
      (LinearMap.ker (chainMap V A 0 (Fin.last N) (Fin.zero_le (Fin.last N)))))
    (p : Fin N) :
    (lowerRightBlock
      (throughSubspaceAdaptedEdgeMatrix V A U₀ hU₀.disjoint
        (throughSubspaceEndpointChartDataOfFiniteDimensional V A U₀ hU₀) p)).rank =
      Module.finrank K (LinearMap.range (A p)) - Module.finrank K U₀ := by
  let data := throughSubspaceEndpointChartDataOfFiniteDimensional V A U₀ hU₀
  let M := throughSubspaceAdaptedEdgeMatrix V A U₀ hU₀.disjoint data p
  have hMform : identityCornerForm M :=
    identityCornerForm_throughSubspaceAdaptedEdgeMatrix V A U₀ hU₀.disjoint data p
  have hMrank : M.rank = Module.finrank K (LinearMap.range (A p)) := by
    dsimp [M, throughSubspaceAdaptedEdgeMatrix]
    exact rank_toMatrix_eq_finrank_range _ _ (A p)
  rcases hMform with ⟨Bmat, Dmat, hM⟩
  have hD : lowerRightBlock M = Dmat := by
    rw [hM]
    rfl
  have hMrank' :
      (fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        Bmat 0 Dmat).rank =
        Module.finrank K (LinearMap.range (A p)) := by
    simpa [M, hM] using hMrank
  have hschur := rank_schurComplement_eq_sub_rank_fromBlocks
    (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K) Bmat
    (0 : Matrix
      (throughSubspaceEndpointComplementIndex V A U₀ p.succ)
      (Fin (Module.finrank K U₀)) K) Dmat (by simp) hMrank'
  change (lowerRightBlock M).rank =
    Module.finrank K (LinearMap.range (A p)) - Module.finrank K U₀
  simpa [hD] using hschur

end EndpointRank

section PaperEndpoint

universe u v

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

/-- The full Aoyagi-order product, viewed on the reversed source-to-target vertex family. -/
abbrev paperTotalMap : reverseVertex W 0 →ₗ[K] reverseVertex W (Fin.last N) :=
  paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
    (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N)))

/-- A paper-order kernel complement as the corresponding reversed-chain kernel complement. -/
abbrev paperEndpointReverseIsCompl
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    IsCompl U₀
      (LinearMap.ker
        (chainMap (reverseVertex W) (reverseEdge W B) 0 (Fin.last N)
          (Fin.zero_le (Fin.last N)))) :=
  isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap W B U₀ hU₀

/-- Endpoint-compatible adapted chart data for one fixed paper-order chain. -/
abbrev paperEndpointChartData
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    ThroughSubspaceChartData (reverseVertex W) (reverseEdge W B) U₀
      (Fin (Module.finrank K U₀))
      (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀) :=
  throughSubspaceEndpointChartDataOfFiniteDimensional
    (reverseVertex W) (reverseEdge W B) U₀
    (paperEndpointReverseIsCompl W B U₀ hU₀)

/-- The endpoint-compatible adapted matrix of one fixed paper-order edge. -/
abbrev paperEndpointAdaptedEdgeMatrix
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
  throughSubspaceAdaptedEdgeMatrix (reverseVertex W) (reverseEdge W B) U₀
    (paperEndpointReverseIsCompl W B U₀ hU₀).disjoint
    (paperEndpointChartData W B U₀ hU₀) p

/-- The upper-unitriangular multiplier for an endpoint-compatible adapted paper edge. -/
abbrev paperEndpointUnitriangularLeft
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0)) (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K) :
    Matrix
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
      (Fin (Module.finrank K U₀) ⊕
        throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K :=
  fromBlocks (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
    (-F) 0 1

/-- The endpoint-compatible adapted matrix of the fixed total paper product. -/
abbrev paperEndpointAdaptedTotalMatrix
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
    (throughSubspaceAdaptedBasis (reverseVertex W) (reverseEdge W B) U₀
      (paperEndpointReverseIsCompl W B U₀ hU₀).disjoint
      (paperEndpointChartData W B U₀ hU₀) 0)
    (throughSubspaceAdaptedBasis (reverseVertex W) (reverseEdge W B) U₀
      (paperEndpointReverseIsCompl W B U₀ hU₀).disjoint
      (paperEndpointChartData W B U₀ hU₀) (Fin.last N))
    (paperTotalMap W B)

omit [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K] in
/-- An endpoint-compatible adapted paper edge has identity-corner form. -/
theorem identityCornerForm_paperEndpointAdaptedEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) :
    identityCornerForm (paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p) := by
  exact identityCornerForm_throughSubspaceAdaptedEdgeMatrix
    (reverseVertex W) (reverseEdge W B) U₀
    (paperEndpointReverseIsCompl W B U₀ hU₀).disjoint
    (paperEndpointChartData W B U₀ hU₀) p

omit [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K] in
/-- An endpoint-compatible adapted paper edge lies in the selected determinant chart. -/
theorem identityCornerDetChart_paperEndpointAdaptedEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) :
    identityCornerDetChart (paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerDetChart_of_identityCornerForm
    (identityCornerForm_paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p)

/-- The selected determinant chart is a neighborhood of an endpoint-compatible adapted edge. -/
theorem paperEndpointAdaptedEdgeMatrix_mem_nhds_identityCornerDetChart
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
      nhds (paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerDetChart_mem_nhds
    (identityCornerDetChart_paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p)

omit [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K] in
/-- Unitriangularly transforming an endpoint-compatible adapted edge preserves
identity-corner form. -/
theorem identityCornerForm_unitriangular_paperEndpointAdaptedEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K) :
    identityCornerForm
      (paperEndpointUnitriangularLeft W B U₀ p F *
        paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerForm_upperUnitriangular_mul F
    (identityCornerForm_paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p)

omit [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K] in
/-- A unitriangularly transformed endpoint-compatible edge lies in the determinant chart. -/
theorem identityCornerDetChart_unitriangular_paperEndpointAdaptedEdgeMatrix
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K) :
    identityCornerDetChart
      (paperEndpointUnitriangularLeft W B U₀ p F *
        paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerDetChart_of_identityCornerForm
    (identityCornerForm_unitriangular_paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p F)

/-- The determinant chart is a neighborhood of a transformed endpoint-compatible edge. -/
theorem unitriangular_paperEndpointAdaptedEdgeMatrix_mem_nhds_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K) :
    {M : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K |
      identityCornerDetChart M} ∈
      nhds
        (paperEndpointUnitriangularLeft W B U₀ p F *
          paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerDetChart_mem_nhds
    (identityCornerDetChart_unitriangular_paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p F)

set_option linter.unusedDecidableInType false in
omit [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K] in
/-- The residual block of an endpoint-compatible adapted paper edge has source
rank minus through-rank. -/
theorem lowerRightBlock_paperEndpointAdaptedEdgeMatrix_rank_eq_sub
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (p : Fin N) :
    (lowerRightBlock (paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p)).rank =
      Module.finrank K (LinearMap.range (reverseEdge W B p)) - Module.finrank K U₀ := by
  exact lowerRightBlock_throughSubspaceEndpointAdaptedEdgeMatrix_rank_eq_sub
    (reverseVertex W) (reverseEdge W B) U₀
    (paperEndpointReverseIsCompl W B U₀ hU₀) p

omit [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K] in
/-- The endpoint-compatible adapted total paper product is `[I 0; 0 0]` at the basepoint. -/
theorem paperEndpointAdaptedTotalMatrix_eq_fromBlocks_one_zero_zero
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    paperEndpointAdaptedTotalMatrix W B U₀ hU₀ =
      fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        (0 : Matrix (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0)
          K)
        (0 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (Fin (Module.finrank K U₀)) K)
        (0 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0)
          K) := by
  simpa [paperEndpointAdaptedTotalMatrix, paperTotalMap, chainMap_reverse_eq_paper] using
    (toMatrix_chainMap_zero_last_endpointChartData_eq_fromBlocks_one_zero_zero
      (reverseVertex W) (reverseEdge W B) U₀
      (paperEndpointReverseIsCompl W B U₀ hU₀))

omit [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K] in
/-- Endpoint-compatible suffix-chain right elimination for the fixed total paper product. -/
theorem productReduction_paperEndpointAdaptedTotalMatrix_suffixChain_rightElim
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    ∃ Bmat : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K,
      ∃ Dmat : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0)
          K,
        paperEndpointAdaptedTotalMatrix W B U₀ hU₀ *
            fromBlocks
              (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
              (-Bmat) 0
              (1 : Matrix
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0)
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            0 0 Dmat := by
  simpa [paperEndpointAdaptedTotalMatrix, paperTotalMap] using
    (productReduction_paperChainMap_endpointChartData_suffixChain_rightElim W B U₀ hU₀)

/-- A fixed-chain, endpoint-compatible certificate for the elementary Aoyagi reduction data. -/
structure PaperEndpointBasepointCertificate
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) : Prop where
  finrank_eq_range :
    Module.finrank K U₀ = Module.finrank K (LinearMap.range (paperTotalMap W B))
  edge_identityCornerForm :
    ∀ p : Fin N, identityCornerForm (paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p)
  edge_detChart :
    ∀ p : Fin N, identityCornerDetChart (paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p)
  edge_detChart_mem_nhds :
    ∀ p : Fin N,
      {M : Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K |
        identityCornerDetChart M} ∈
        nhds (paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p)
  unitriangular_edge_detChart :
    ∀ (p : Fin N)
      (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K),
      identityCornerDetChart
        (paperEndpointUnitriangularLeft W B U₀ p F *
          paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p)
  unitriangular_edge_detChart_mem_nhds :
    ∀ (p : Fin N)
      (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        K),
      {M : Matrix
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
          (Fin (Module.finrank K U₀) ⊕
            throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K |
        identityCornerDetChart M} ∈
        nhds
          (paperEndpointUnitriangularLeft W B U₀ p F *
            paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p)
  edge_lowerRight_rank :
    ∀ p : Fin N,
      (lowerRightBlock (paperEndpointAdaptedEdgeMatrix W B U₀ hU₀ p)).rank =
        Module.finrank K (LinearMap.range (reverseEdge W B p)) - Module.finrank K U₀
  total_block :
    paperEndpointAdaptedTotalMatrix W B U₀ hU₀ =
      fromBlocks
        (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
        (0 : Matrix (Fin (Module.finrank K U₀))
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0)
          K)
        (0 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (Fin (Module.finrank K U₀)) K)
        (0 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0)
          K)
  suffix_rightElim :
    ∃ Bmat : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K,
      ∃ Dmat : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0)
          K,
        paperEndpointAdaptedTotalMatrix W B U₀ hU₀ *
            fromBlocks
              (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
              (-Bmat) 0
              (1 : Matrix
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0)
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
          fromBlocks
            (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
            0 0 Dmat

/-- Any chosen total-kernel complement gives the fixed-chain endpoint basepoint certificate. -/
theorem paperEndpointBasepointCertificate_of_isCompl
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))) :
    PaperEndpointBasepointCertificate W B U₀ hU₀ where
  finrank_eq_range :=
    (LinearMap.kerComplementEquivRange (paperTotalMap W B) hU₀).finrank_eq
  edge_identityCornerForm := identityCornerForm_paperEndpointAdaptedEdgeMatrix W B U₀ hU₀
  edge_detChart := identityCornerDetChart_paperEndpointAdaptedEdgeMatrix W B U₀ hU₀
  edge_detChart_mem_nhds :=
    paperEndpointAdaptedEdgeMatrix_mem_nhds_identityCornerDetChart W B U₀ hU₀
  unitriangular_edge_detChart :=
    identityCornerDetChart_unitriangular_paperEndpointAdaptedEdgeMatrix W B U₀ hU₀
  unitriangular_edge_detChart_mem_nhds :=
    unitriangular_paperEndpointAdaptedEdgeMatrix_mem_nhds_identityCornerDetChart
      W B U₀ hU₀
  edge_lowerRight_rank :=
    lowerRightBlock_paperEndpointAdaptedEdgeMatrix_rank_eq_sub W B U₀ hU₀
  total_block := paperEndpointAdaptedTotalMatrix_eq_fromBlocks_one_zero_zero W B U₀ hU₀
  suffix_rightElim :=
    productReduction_paperEndpointAdaptedTotalMatrix_suffixChain_rightElim W B U₀ hU₀

/-- Finite-dimensional paper-order chains admit an endpoint basepoint certificate. -/
theorem exists_paperEndpointBasepointCertificate
    [∀ j, FiniteDimensional K (W j)] :
    ∃ U₀ : Submodule K (reverseVertex W 0),
      ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
        PaperEndpointBasepointCertificate W B U₀ hU₀ := by
  rcases exists_isCompl_ker_paperEndpointChartDataOfFiniteDimensional W B with
    ⟨U₀, hU₀, _, _⟩
  exact ⟨U₀, hU₀, paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀⟩

end PaperEndpoint

end Aoyagi
end DLN
end DLNFibre
