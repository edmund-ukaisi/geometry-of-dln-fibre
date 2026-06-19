import DLNFibre.DLN.Aoyagi.ThroughLayerMatrix
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Instances.Matrix

/-!
# Topological determinant charts for Aoyagi product reduction

This file records the elementary open-neighborhood facts for the selected
top-left determinant chart.  It does not state rank-stratum or RLCT
consequences.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

section DeterminantChart

variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K]
variable {ι μ ν : Type*} [Fintype ι] [DecidableEq ι]

omit [IsTopologicalRing K] in
/-- The unit locus in a ring with open units is open. -/
theorem isOpen_setOf_isUnit : IsOpen ({x : K | IsUnit x}) := by
  simpa [IsUnit] using (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).isOpen_range

omit [CommRing K] [IsTopologicalRing K] [IsOpenUnits K] [Fintype ι] [DecidableEq ι] in
/-- The selected top-left corner is a continuous function of the matrix entries. -/
theorem continuous_topLeftCorner :
    Continuous (fun M : Matrix (ι ⊕ μ) (ι ⊕ ν) K ↦ topLeftCorner M) := by
  exact continuous_id.matrix_submatrix Sum.inl Sum.inl

omit [IsOpenUnits K] in
/-- The determinant of the selected top-left corner is continuous. -/
theorem continuous_det_topLeftCorner :
    Continuous (fun M : Matrix (ι ⊕ μ) (ι ⊕ ν) K ↦ (topLeftCorner M).det) :=
  continuous_topLeftCorner.matrix_det

/-- The selected determinant chart is open in the ambient matrix space. -/
theorem isOpen_identityCornerDetChart :
    IsOpen ({M : Matrix (ι ⊕ μ) (ι ⊕ ν) K | identityCornerDetChart M}) := by
  dsimp [identityCornerDetChart]
  exact continuous_det_topLeftCorner.isOpen_preimage _ isOpen_setOf_isUnit

/-- A point in the selected determinant chart has that chart as a neighborhood. -/
theorem identityCornerDetChart_mem_nhds
    {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K} (hM : identityCornerDetChart M) :
    {N : Matrix (ι ⊕ μ) (ι ⊕ ν) K | identityCornerDetChart N} ∈ nhds M :=
  IsOpen.mem_nhds isOpen_identityCornerDetChart hM

/-- Left multiplication pulls the selected determinant chart back to a neighborhood of
the untransformed matrix. -/
theorem leftMul_identityCornerDetChart_mem_nhds
    [Fintype μ]
    (A : Matrix (ι ⊕ μ) (ι ⊕ μ) K)
    {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K}
    (hAM : identityCornerDetChart (A * M)) :
    {N : Matrix (ι ⊕ μ) (ι ⊕ ν) K | identityCornerDetChart (A * N)} ∈ nhds M := by
  exact (continuous_const.matrix_mul continuous_id).continuousAt.preimage_mem_nhds
    (identityCornerDetChart_mem_nhds hAM)

/-- Upper-block left multiplication pulls the selected determinant chart back to a
neighborhood of the untransformed matrix. -/
theorem fromBlocks_leftMul_identityCornerDetChart_mem_nhds
    [Fintype μ] [DecidableEq μ]
    (F : Matrix ι μ K)
    {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K}
    (hFM : identityCornerDetChart
      (fromBlocks (1 : Matrix ι ι K) F 0 (1 : Matrix μ μ K) * M)) :
    {N : Matrix (ι ⊕ μ) (ι ⊕ ν) K |
      identityCornerDetChart
        (fromBlocks (1 : Matrix ι ι K) F 0 (1 : Matrix μ μ K) * N)} ∈ nhds M :=
  leftMul_identityCornerDetChart_mem_nhds
    (fromBlocks (1 : Matrix ι ι K) F 0 (1 : Matrix μ μ K)) hFM

/-- Identity-corner form gives an open determinant-chart neighborhood of the matrix. -/
theorem identityCornerForm_mem_nhds_identityCornerDetChart
    {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K} (hM : identityCornerForm M) :
    {N : Matrix (ι ⊕ μ) (ι ⊕ ν) K | identityCornerDetChart N} ∈ nhds M :=
  identityCornerDetChart_mem_nhds (identityCornerDetChart_of_identityCornerForm hM)

end DeterminantChart

section PaperOrder

universe u v

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [IsOpenUnits K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

/-- An adapted paper-order edge has an open selected determinant-chart neighborhood. -/
theorem paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N) :
    {M : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K |
      identityCornerDetChart M} ∈
      nhds (paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerDetChart_mem_nhds
    (identityCornerDetChart_paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p)

/-- A transformed adapted paper-order edge has an open determinant-chart neighborhood. -/
theorem unitriangular_paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart
    [∀ j, FiniteDimensional K (W j)]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : Disjoint U₀
      (LinearMap.ker
        (paperChainMap W B (Fin.last N).rev (0 : Fin (N + 1)).rev
          (Fin.rev_le_rev.mpr (Fin.zero_le (Fin.last N))))))
    (p : Fin N)
    (F : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ) K) :
    {M : Matrix
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.succ)
        (Fin (Module.finrank K U₀) ⊕
          throughSubspaceComplementIndex (reverseVertex W) (reverseEdge W B) U₀ p.castSucc) K |
      identityCornerDetChart M} ∈
      nhds (paperUnitriangularLeft W B U₀ p F * paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p) :=
  identityCornerDetChart_mem_nhds
    (identityCornerDetChart_unitriangular_paperAdaptedReverseEdgeMatrix W B U₀ hU₀ p F)

end PaperOrder

end Aoyagi
end DLN
end DLNFibre
