import DLNFibre.DLN.Aoyagi.EntryIdeal
import DLNFibre.DLN.Aoyagi.ProductReductionBoundary

/-!
# Entry-ideal boundary for Aoyagi product reduction

This file converts the fixed-base endpoint product-difference block identity
into an equality of scalar matrix-entry ideals.  It remains an algebraic
boundary statement: no analytic germ ideal, normal-crossing, pole-order, or
RLCT consequence is asserted here.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

section GenericProductDifferenceEntryIdeal

variable {R : Type*} [CommRing R]

/-- Determinant-unit triangular endpoint multiplication transports the
product-difference entry ideal to the cleaned four-block ideal. -/
theorem matrixEntryIdeal_triangularBlockProductDifference_eq_fourMatrixEntryIdeal
    {ι μ ν : Type*} [Fintype ι] [Fintype μ] [Fintype ν]
    [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]
    (F2 : Matrix ι ν R) (F3 : Matrix μ ι R)
    (Ctop : Matrix ι ι R) (D : Matrix μ ν R)
    (T : Matrix (ι ⊕ μ) (ι ⊕ ν) R)
    (hLeft :
      IsUnit
        (fromBlocks (1 : Matrix ι ι R) 0 F3 (1 : Matrix μ μ R)).det)
    (hRight :
      IsUnit
        (fromBlocks (1 : Matrix ι ι R) F2 0 (1 : Matrix ν ν R)).det)
    (htri :
      fromBlocks (1 : Matrix ι ι R) 0 F3 (1 : Matrix μ μ R) * T *
        fromBlocks (1 : Matrix ι ι R) F2 0 (1 : Matrix ν ν R) =
          fromBlocks Ctop 0 0 D) :
    matrixEntryIdeal
        (T - fromBlocks (1 : Matrix ι ι R) 0
          (0 : Matrix μ ι R) (0 : Matrix μ ν R)) =
      fourMatrixEntryIdeal (Ctop - 1) F2 F3 D := by
  let L : Matrix (ι ⊕ μ) (ι ⊕ μ) R :=
    fromBlocks (1 : Matrix ι ι R) 0 F3 (1 : Matrix μ μ R)
  let Rmat : Matrix (ι ⊕ ν) (ι ⊕ ν) R :=
    fromBlocks (1 : Matrix ι ι R) F2 0 (1 : Matrix ν ν R)
  let T0 : Matrix (ι ⊕ μ) (ι ⊕ ν) R :=
    fromBlocks (1 : Matrix ι ι R) 0 (0 : Matrix μ ι R) (0 : Matrix μ ν R)
  have hLeft' : IsUnit L.det := by
    exact hLeft
  have hRight' : IsUnit Rmat.det := by
    exact hRight
  have hdiff :
      L * (T - T0) * Rmat =
        fromBlocks (Ctop - 1) (-F2) (-F3) (D - F3 * F2) := by
    simpa [L, Rmat, T0] using
      triangularBlockProductDifference_fromBlocks_indexed
        F2 F3 Ctop D T htri
  have htransport :
      matrixEntryIdeal (L * (T - T0) * Rmat) =
        matrixEntryIdeal (T - T0) := by
    exact
      (matrixEntryIdeal_mul_right_eq_of_isUnit_det (L * (T - T0)) Rmat hRight').trans
        (matrixEntryIdeal_mul_left_eq_of_isUnit_det L (T - T0) hLeft')
  calc
    matrixEntryIdeal (T - T0) =
        matrixEntryIdeal (L * (T - T0) * Rmat) := htransport.symm
    _ = matrixEntryIdeal (fromBlocks (Ctop - 1) (-F2) (-F3) (D - F3 * F2)) := by
      rw [hdiff]
    _ = fourMatrixEntryIdeal (Ctop - 1) F2 F3 D :=
      matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_fourMatrixEntryIdeal
        (Ctop - 1) F2 F3 D

end GenericProductDifferenceEntryIdeal

section FixedBaseProductDifferenceEntryIdealBoundary

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

universe u v

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)] [∀ i, T2Space (W i)]
  [∀ i, Module K (W i)] [∀ i, ContinuousSMul K (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[K] W i.castSucc)

/-- Source-shaped endpoint conclusion after applying the product-difference
entry-ideal cleanup to the triangular residual-product certificate. -/
structure PaperEndpointFixedBaseProductDifferenceEntryIdealSourceRanks
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) (x : α) : Prop where
  productDifferenceEntryIdeal :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    ∃ F2 : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K,
      ∃ F3 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (Fin (Module.finrank K U₀)) K,
        ∃ Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K,
          IsUnit
              (fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                0 F3
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K)).det ∧
            IsUnit
              (fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                F2 0
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0)
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0) K)).det ∧
            IsUnit Ctop.det ∧
            matrixEntryIdeal
                (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
                  fromBlocks
                    (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                    0
                    (0 : Matrix
                      (throughSubspaceEndpointComplementIndex
                        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                      (Fin (Module.finrank K U₀)) K)
                    (0 : Matrix
                      (throughSubspaceEndpointComplementIndex
                        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                      (throughSubspaceEndpointComplementIndex
                        (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
              fourMatrixEntryIdeal (Ctop - 1) F2 F3
                (ChartLocalSuffixState.residualProduct EMat (Fin.last N) 0
                  (Fin.zero_le (Fin.last N)))
  sourceResidualRanks :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    ∀ p : Fin N,
      (ChartLocalSuffixState.residualBlock EMat (Fin.last N) p p.succ.le_last).rank =
        rEdge p - r

namespace PaperEndpointFixedBaseTriangularResidualProductSourceRanks

set_option linter.unusedSectionVars false in
/-- The triangular residual-product/source-rank boundary exposes the
product-difference entry ideal. -/
theorem exists_productDifferenceEntryIdeal
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (cert :
      PaperEndpointFixedBaseTriangularResidualProductSourceRanks
        W B U₀ hU₀ Cedge r rEdge x) :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    ∃ F2 : Matrix (Fin (Module.finrank K U₀))
        (throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ 0) K,
      ∃ F3 : Matrix
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (Fin (Module.finrank K U₀)) K,
        ∃ Ctop : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K,
          IsUnit
              (fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                0 F3
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K)).det ∧
            IsUnit
              (fromBlocks
                (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                F2 0
                (1 : Matrix
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0)
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0) K)).det ∧
            IsUnit Ctop.det ∧
            matrixEntryIdeal
                (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E -
                  fromBlocks
                    (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
                    0
                    (0 : Matrix
                      (throughSubspaceEndpointComplementIndex
                        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                      (Fin (Module.finrank K U₀)) K)
                    (0 : Matrix
                      (throughSubspaceEndpointComplementIndex
                        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                      (throughSubspaceEndpointComplementIndex
                        (reverseVertex W) (reverseEdge W B) U₀ 0) K)) =
              fourMatrixEntryIdeal (Ctop - 1) F2 F3
                (ChartLocalSuffixState.residualProduct EMat (Fin.last N) 0
                  (Fin.zero_le (Fin.last N))) := by
  classical
  dsimp
  rcases cert.triangularResidualProduct with
    ⟨F2, F3, Ctop, hLeft, hRight, hCtop, htri⟩
  refine ⟨F2, F3, Ctop, hLeft, hRight, hCtop, ?_⟩
  exact
    matrixEntryIdeal_triangularBlockProductDifference_eq_fourMatrixEntryIdeal
      F2 F3 Ctop
      (ChartLocalSuffixState.residualProduct
        (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
          (fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)))
        (Fin.last N) 0 (Fin.zero_le (Fin.last N)))
      (paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀
        (fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)))
      hLeft hRight htri

set_option linter.unusedSectionVars false in
/-- Package the product-difference entry-ideal handoff together with the
source residual-rank equalities. -/
theorem toProductDifferenceEntryIdealSourceRanks
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (cert :
      PaperEndpointFixedBaseTriangularResidualProductSourceRanks
        W B U₀ hU₀ Cedge r rEdge x) :
    PaperEndpointFixedBaseProductDifferenceEntryIdealSourceRanks
      W B U₀ hU₀ Cedge r rEdge x where
  productDifferenceEntryIdeal :=
    cert.exists_productDifferenceEntryIdeal (W := W) (B := B)
  sourceResidualRanks := cert.sourceResidualRanks

end PaperEndpointFixedBaseTriangularResidualProductSourceRanks

set_option linter.unusedSectionVars false in
/-- Near a continuous edge family based at `B`, the product-difference entry-ideal
source-rank package holds relative to Aoyagi's source-shaped rank stratum. -/
theorem paperEndpointFixedBaseProductDifferenceEntryIdeal_selfBase_mem_nhdsWithin_source
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    {x : α |
      PaperEndpointFixedBaseProductDifferenceEntryIdealSourceRanks
        W B U₀ hU₀ Cedge r rEdge x} ∈
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge) := by
  exact Filter.mem_of_superset
    (paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source
      W B U₀ hU₀ Cedge r rEdge hCedge hbase)
    (by
      intro x hx
      exact
        PaperEndpointFixedBaseTriangularResidualProductSourceRanks.toProductDifferenceEntryIdealSourceRanks
          (W := W) (B := B) hx)

/-- A continuous reversed-edge family based at `B` admits a local
product-difference entry-ideal/source-rank package, relative to Aoyagi's source
rank stratum, after choosing endpoint bases from a total-kernel complement. -/
def PaperEndpointProductDifferenceEntryIdealLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Prop :=
  ∃ U₀ : Submodule K (reverseVertex W 0),
    ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
      {x : α |
        PaperEndpointFixedBaseProductDifferenceEntryIdealSourceRanks
          W B U₀ hU₀ Cedge r rEdge x} ∈
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)

set_option linter.unusedSectionVars false in
/-- Finite-dimensional paper chains admit the local product-difference
entry-ideal/source-rank package near any continuous reversed-edge family based
at the chain. -/
theorem exists_paperEndpointProductDifferenceEntryIdealLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    PaperEndpointProductDifferenceEntryIdealLocalCertificate W B x₀ Cedge r rEdge := by
  rcases exists_paperEndpointBasepointCertificate W B with ⟨U₀, hU₀, _⟩
  exact ⟨U₀, hU₀,
    paperEndpointFixedBaseProductDifferenceEntryIdeal_selfBase_mem_nhdsWithin_source
      W B U₀ hU₀ Cedge r rEdge hCedge hbase⟩

end FixedBaseProductDifferenceEntryIdealBoundary

end Aoyagi
end DLN
end DLNFibre
