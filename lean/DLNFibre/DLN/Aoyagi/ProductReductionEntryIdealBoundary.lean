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

/-- Determinant-unit triangular endpoint multiplication transports the
product-difference entry ideal to the regular-block entry ideal joined with the
residual block-entry ideal. -/
theorem matrixEntryIdeal_triangularBlockProductDifference_eq_regular_sup_residual
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
      regularBlockEntryIdeal (Ctop - 1) F2 F3 ⊔ matrixEntryIdeal D := by
  calc
    matrixEntryIdeal
        (T - fromBlocks (1 : Matrix ι ι R) 0
          (0 : Matrix μ ι R) (0 : Matrix μ ν R)) =
        fourMatrixEntryIdeal (Ctop - 1) F2 F3 D :=
      matrixEntryIdeal_triangularBlockProductDifference_eq_fourMatrixEntryIdeal
        F2 F3 Ctop D T hLeft hRight htri
    _ = regularBlockEntryIdeal (Ctop - 1) F2 F3 ⊔ matrixEntryIdeal D :=
      fourMatrixEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
        (Ctop - 1) F2 F3 D

namespace ChartLocalSuffixState

/-- A deterministic block-diagonal suffix state exposes the product-difference
entry ideal with canonical coefficient fields. -/
theorem productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) R)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) R)
    {i j : Fin (N + 1)} (hij : i ≤ j)
    (hS : (suffixState E j i hij).BlockDiagonal P hij) :
    let S : ChartLocalSuffixState ρ κ R j i := suffixState E j i hij
    matrixEntryIdeal
        (P i j hij - fromBlocks (1 : Matrix ρ ρ R) 0
          (0 : Matrix (κ j) ρ R) (0 : Matrix (κ j) (κ i) R)) =
      fourMatrixEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D := by
  classical
  let S : ChartLocalSuffixState ρ κ R j i := suffixState E j i hij
  have hS' : S.BlockDiagonal P hij := by
    simpa [S] using hS
  have hSL :
      S.L =
        fromBlocks (1 : Matrix ρ ρ R) 0 (lowerLeftBlock S.L)
          (1 : Matrix (κ j) (κ j) R) := by
    rcases suffixState_L_eq_lowerUnitriangular (K := R) E hij with ⟨F3, hF3⟩
    rw [hF3]
    rfl
  have hLeft :
      IsUnit
        (fromBlocks (1 : Matrix ρ ρ R) 0 (lowerLeftBlock S.L)
          (1 : Matrix (κ j) (κ j) R)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks (1 : Matrix ρ ρ R) 0 (lowerLeftBlock S.L)
          (1 : Matrix (κ j) (κ j) R))).mp
      ((Matrix.isUnit_fromBlocks_zero₁₂).2 ⟨isUnit_one, isUnit_one⟩)
  have hRight :
      IsUnit
        (fromBlocks (1 : Matrix ρ ρ R) (-S.B) 0
          (1 : Matrix (κ i) (κ i) R)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks (1 : Matrix ρ ρ R) (-S.B) 0
          (1 : Matrix (κ i) (κ i) R))).mp
      ((Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩)
  rcases hS' with ⟨_, _, hdiag⟩
  have htri :
      fromBlocks (1 : Matrix ρ ρ R) 0 (lowerLeftBlock S.L)
          (1 : Matrix (κ j) (κ j) R) *
        P i j hij *
      fromBlocks (1 : Matrix ρ ρ R) (-S.B) 0
          (1 : Matrix (κ i) (κ i) R) =
        fromBlocks S.Ctop 0 0 S.D := by
    rw [← hSL]
    exact hdiag
  simpa [S] using
    matrixEntryIdeal_triangularBlockProductDifference_eq_fourMatrixEntryIdeal
      (-S.B) (lowerLeftBlock S.L) S.Ctop S.D (P i j hij) hLeft hRight htri

/-- A deterministic block-diagonal suffix state exposes the product-difference
entry ideal as the regular-block entry ideal joined with the residual
block-entry ideal. -/
theorem productDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) R)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) R)
    {i j : Fin (N + 1)} (hij : i ≤ j)
    (hS : (suffixState E j i hij).BlockDiagonal P hij) :
    let S : ChartLocalSuffixState ρ κ R j i := suffixState E j i hij
    matrixEntryIdeal
        (P i j hij - fromBlocks (1 : Matrix ρ ρ R) 0
          (0 : Matrix (κ j) ρ R) (0 : Matrix (κ j) (κ i) R)) =
      regularBlockEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
        matrixEntryIdeal S.D := by
  intro S
  calc
    matrixEntryIdeal
        (P i j hij - fromBlocks (1 : Matrix ρ ρ R) 0
          (0 : Matrix (κ j) ρ R) (0 : Matrix (κ j) (κ i) R)) =
        fourMatrixEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D := by
      simpa [S] using
        productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal
          (E := E) (P := P) (hij := hij) hS
    _ = regularBlockEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
        matrixEntryIdeal S.D :=
      fourMatrixEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
        (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D

end ChartLocalSuffixState

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

namespace PaperEndpointFixedBaseProductReductionCertificate

set_option linter.unusedSectionVars false in
/-- The fixed-base endpoint certificate exposes the product-difference entry
ideal using the deterministic suffix-state fields. -/
theorem productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal_canonicalFields
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {rEdge : Fin N → ℕ} {x : α}
    (cert : PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x) :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    let S := ChartLocalSuffixState.suffixState EMat
      (Fin.last N) 0 (Fin.zero_le (Fin.last N))
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
      fourMatrixEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D := by
  classical
  let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
  let P := paperEndpointFixedBaseChainMapMatrixOfReverseEdges W B U₀ hU₀ E
  let S := ChartLocalSuffixState.suffixState EMat
    (Fin.last N) 0 (Fin.zero_le (Fin.last N))
  have hS :
      S.BlockDiagonal P (Fin.zero_le (Fin.last N)) := by
    simpa [ChartLocalSuffixState.BlockDiagonal,
      paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal, E, EMat, P, S,
      paperEndpointFixedBaseTotalMatrixOfReverseEdges_eq_chainMapMatrix] using
        cert.blockDiagonal
  simpa [E, EMat, P, S,
    paperEndpointFixedBaseTotalMatrixOfReverseEdges_eq_chainMapMatrix] using
    ChartLocalSuffixState.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal
      (E := EMat) (P := P) (hij := Fin.zero_le (Fin.last N)) hS

end PaperEndpointFixedBaseProductReductionCertificate

set_option linter.unusedSectionVars false in
/-- The canonical product-difference coefficient fields vary continuously in
fixed endpoint bases under the recursive determinant-chart hypotheses. -/
theorem paperEndpointFixedBaseContinuousEdges_productDifferenceCoefficientFields_continuousAt
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
    let S : α →
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    IsUnit ((S x₀).Ctop.det) ∧
      ContinuousAt (fun x : α ↦ (S x).Ctop - 1) x₀ ∧
      ContinuousAt (fun x : α ↦ -(S x).B) x₀ ∧
      ContinuousAt (fun x : α ↦ lowerLeftBlock (S x).L) x₀ ∧
      ContinuousAt (fun x : α ↦ (S x).D) x₀ := by
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
  let S : α →
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  have hfields :
      IsUnit ((S x₀).Ctop.det) ∧
        ContinuousAt (fun x : α ↦ (S x).L) x₀ ∧
        ContinuousAt (fun x : α ↦ (S x).B) x₀ ∧
        ContinuousAt (fun x : α ↦ (S x).Ctop) x₀ ∧
        ContinuousAt (fun x : α ↦ (S x).D) x₀ := by
    simpa [E, S] using
      (paperEndpointFixedBaseContinuousEdges_recursiveSuffixState_fields_continuousAt
        W B U₀ hU₀ Cedge hCedge hchart₀
        (i := 0) (hi := Fin.zero_le (Fin.last N)))
  rcases hfields with ⟨hunit, hL, hB, hCtop, hD⟩
  refine ⟨hunit, ?_, ?_, ?_, hD⟩
  · simpa [S] using hCtop.sub continuousAt_const
  · simpa [S] using hB.neg
  · have hlower :
        Continuous
          (fun M :
            Matrix
              (Fin (Module.finrank K U₀) ⊕
                throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (Fin (Module.finrank K U₀) ⊕
                throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K ↦
            lowerLeftBlock M) :=
      continuous_id.matrix_submatrix Sum.inr Sum.inl
    simpa [S] using hlower.continuousAt.comp hL

set_option linter.unusedSectionVars false in
/-- At the base chain, the canonical product-difference coefficient fields vary
continuously in fixed endpoint bases. -/
theorem paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
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
    let S : α →
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    IsUnit ((S x₀).Ctop.det) ∧
      ContinuousAt (fun x : α ↦ (S x).Ctop - 1) x₀ ∧
      ContinuousAt (fun x : α ↦ -(S x).B) x₀ ∧
      ContinuousAt (fun x : α ↦ lowerLeftBlock (S x).L) x₀ ∧
      ContinuousAt (fun x : α ↦ (S x).D) x₀ := by
  exact
    paperEndpointFixedBaseContinuousEdges_productDifferenceCoefficientFields_continuousAt
      W B U₀ hU₀ Cedge hCedge
      (paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_detChart
        W B U₀ hU₀ Cedge hbase)

set_option linter.unusedSectionVars false in
/-- At the base chain, the canonical product-difference coefficient fields are
centered and continuous in fixed endpoint bases. -/
theorem paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_centered_continuousAt
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
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
    let S : α →
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    (S x₀).Ctop - 1 = 0 ∧
      -(S x₀).B = 0 ∧
      lowerLeftBlock (S x₀).L = 0 ∧
      (S x₀).D = 0 ∧
      IsUnit ((S x₀).Ctop.det) ∧
      ContinuousAt (fun x : α ↦ (S x).Ctop - 1) x₀ ∧
      ContinuousAt (fun x : α ↦ -(S x).B) x₀ ∧
      ContinuousAt (fun x : α ↦ lowerLeftBlock (S x).L) x₀ ∧
      ContinuousAt (fun x : α ↦ (S x).D) x₀ := by
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
  let S : α →
      ChartLocalSuffixState (Fin (Module.finrank K U₀))
        (fun j : Fin (N + 1) ↦
          throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
        K (Fin.last N) 0 :=
    fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
      (Fin.zero_le (Fin.last N))
  have hcont :
      IsUnit ((S x₀).Ctop.det) ∧
        ContinuousAt (fun x : α ↦ (S x).Ctop - 1) x₀ ∧
        ContinuousAt (fun x : α ↦ -(S x).B) x₀ ∧
        ContinuousAt (fun x : α ↦ lowerLeftBlock (S x).L) x₀ ∧
        ContinuousAt (fun x : α ↦ (S x).D) x₀ := by
    simpa [E, S] using
      paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_continuousAt
        W B U₀ hU₀ Cedge hCedge hbase
  let E₀ : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
    fun p ↦ (Cedge x₀ p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
  have hchart₀ : ∀ p : Fin N,
      identityCornerDetChart
        (ChartLocalSuffixState.transformedEdge
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E₀)
          p
          (ChartLocalSuffixState.suffixState
            (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E₀)
            (Fin.last N) p.succ p.succ.le_last)) := by
    simpa [E₀, E] using
      paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_detChart
        W B U₀ hU₀ Cedge hbase
  have hblock :
      let S₀ := ChartLocalSuffixState.suffixState
        (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E₀)
        (Fin.last N) 0 (Fin.zero_le (Fin.last N))
      IsUnit S₀.L.det ∧ IsUnit S₀.Ctop.det ∧
        S₀.L * paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E₀ *
            fromBlocks
              (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
              (-S₀.B) 0
              (1 : Matrix
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0)
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
          fromBlocks S₀.Ctop 0 0 S₀.D := by
    simpa [E₀] using
      paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal
        W B U₀ hU₀ E₀ hchart₀
  have hE₀ : E₀ = reverseEdge W B := by
    funext p
    dsimp [E₀]
    rw [hbase]
    rfl
  have htotal :
      paperEndpointFixedBaseTotalMatrixOfReverseEdges W B U₀ hU₀ E₀ =
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
              (reverseVertex W) (reverseEdge W B) U₀ 0) K) := by
    rw [hE₀]
    simpa [E₀, paperEndpointFixedBaseTotalMatrixOfReverseEdges,
      paperEndpointAdaptedTotalMatrix, paperTotalMap, chainMap_reverse_eq_paper] using
        paperEndpointAdaptedTotalMatrix_eq_fromBlocks_one_zero_zero W B U₀ hU₀
  rcases hblock with ⟨_hLunit, _hCtopUnit, hdiag⟩
  rcases ChartLocalSuffixState.suffixState_L_eq_lowerUnitriangular
      (K := K) (E x₀) (Fin.zero_le (Fin.last N)) with
    ⟨F3, hL⟩
  have hEMat :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E₀ = E x₀ := by
    funext p
    rfl
  have hdiag' :
      fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          0 F3
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N)) K) *
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
              (reverseVertex W) (reverseEdge W B) U₀ 0) K) *
        fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (-(S x₀).B) 0
          (1 : Matrix
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀ 0)
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0) K) =
          fromBlocks (S x₀).Ctop 0 0 (S x₀).D := by
    simpa [E₀, E, S, hEMat, hL, htotal] using hdiag
  have hblocks :
      fromBlocks
          (1 : Matrix (Fin (Module.finrank K U₀)) (Fin (Module.finrank K U₀)) K)
          (-(S x₀).B) F3 (F3 * (-(S x₀).B)) =
        fromBlocks (S x₀).Ctop 0 0 (S x₀).D := by
    simpa [fromBlocks_multiply, Matrix.mul_assoc] using hdiag'
  rcases Matrix.fromBlocks_inj.mp hblocks with
    ⟨hCtop, hB, hF3, hD⟩
  have hCtop_center : (S x₀).Ctop - 1 = 0 := by
    rw [← hCtop]
    simp
  have hB_center : -(S x₀).B = 0 := hB
  have hF3_center : lowerLeftBlock (S x₀).L = 0 := by
    rw [hL]
    simpa [lowerLeftBlock] using hF3
  have hD_center : (S x₀).D = 0 := by
    rw [← hD, hF3]
    simp
  rcases hcont with ⟨hunit, hCtop_cont, hB_cont, hF3_cont, hD_cont⟩
  exact
    ⟨hCtop_center, hB_center, hF3_center, hD_center, hunit,
      hCtop_cont, hB_cont, hF3_cont, hD_cont⟩

/-- Source-shaped endpoint conclusion using the deterministic canonical
product-difference coefficient fields. -/
structure PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) (x : α) : Prop where
  canonicalProductDifferenceEntryIdeal :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    let S := ChartLocalSuffixState.suffixState EMat
      (Fin.last N) 0 (Fin.zero_le (Fin.last N))
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
      fourMatrixEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D
  sourceResidualRanks :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    ∀ p : Fin N,
      (ChartLocalSuffixState.residualBlock EMat (Fin.last N) p p.succ.le_last).rank =
        rEdge p - r

namespace PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks

set_option linter.unusedSectionVars false in
/-- The canonical product-difference entry ideal splits algebraically into the
three regular block-entry families and the residual `D` block. -/
theorem canonicalProductDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
        W B U₀ hU₀ Cedge r rEdge x) :
    let E : ∀ p : Fin N, reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ :=
      fun p ↦ (Cedge x p : reverseVertex W p.castSucc →ₗ[K] reverseVertex W p.succ)
    let EMat := paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀ E
    let S := ChartLocalSuffixState.suffixState EMat
      (Fin.last N) 0 (Fin.zero_le (Fin.last N))
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
      regularBlockEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
        matrixEntryIdeal S.D := by
  intro E EMat S
  calc
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
        fourMatrixEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D := by
      simpa [E, EMat, S] using cert.canonicalProductDifferenceEntryIdeal
    _ = regularBlockEntryIdeal (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) ⊔
        matrixEntryIdeal S.D :=
      fourMatrixEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal
        (S.Ctop - 1) (-S.B) (lowerLeftBlock S.L) S.D

end PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks

namespace PaperEndpointFixedBaseProductReductionCertificate

set_option linter.unusedSectionVars false in
/-- On Aoyagi's source-shaped rank stratum, the fixed-base endpoint certificate
exposes the canonical product-difference entry ideal and source residual ranks. -/
theorem toCanonicalProductDifferenceSourceRanks
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ} {x : α}
    (base : PaperEndpointBasepointCertificate W B U₀ hU₀)
    (cert : PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x)
    (hsrc : x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge) :
    PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
      W B U₀ hU₀ Cedge r rEdge x where
  canonicalProductDifferenceEntryIdeal :=
    cert.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal_canonicalFields
      (W := W) (B := B)
  sourceResidualRanks := by
    dsimp
    intro p
    simpa using
      PaperEndpointFixedBaseProductReductionCertificate.residualBlock_rank_eq_sourceRankSubProductRank
        (W := W) (B := B) base cert hsrc p

end PaperEndpointFixedBaseProductReductionCertificate

set_option linter.unusedSectionVars false in
/-- Near a continuous edge family based at `B`, the canonical product-difference
source-rank package holds relative to Aoyagi's source-shaped rank stratum. -/
theorem paperEndpointFixedBaseCanonicalProductDifferenceSourceRanks_selfBase_mem_nhdsWithin_source
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
      PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
        W B U₀ hU₀ Cedge r rEdge x} ∈
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge) := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine
    ⟨{x : α |
      PaperEndpointFixedBaseProductReductionCertificate W B U₀ hU₀ Cedge rEdge x},
      paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds
        W B U₀ hU₀ Cedge rEdge hCedge hbase,
      ?_⟩
  intro x hx
  exact
    PaperEndpointFixedBaseProductReductionCertificate.toCanonicalProductDifferenceSourceRanks
      (W := W) (B := B)
      (base := paperEndpointBasepointCertificate_of_isCompl W B U₀ hU₀)
      (cert := hx.1)
      (hsrc := hx.2)

/-- A local fixed-base package for the canonical product-difference fields:
centered continuous coefficient fields at the base point, and pointwise
canonical product-difference/source-rank conclusions on the source rank
stratum. -/
structure PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Prop where
  coefficientFields_centered_continuous :
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
    let S : α →
        ChartLocalSuffixState (Fin (Module.finrank K U₀))
          (fun j : Fin (N + 1) ↦
            throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j)
          K (Fin.last N) 0 :=
      fun x ↦ ChartLocalSuffixState.suffixState (E x) (Fin.last N) 0
        (Fin.zero_le (Fin.last N))
    (S x₀).Ctop - 1 = 0 ∧
      -(S x₀).B = 0 ∧
      lowerLeftBlock (S x₀).L = 0 ∧
      (S x₀).D = 0 ∧
      IsUnit ((S x₀).Ctop.det) ∧
      ContinuousAt (fun x : α ↦ (S x).Ctop - 1) x₀ ∧
      ContinuousAt (fun x : α ↦ -(S x).B) x₀ ∧
      ContinuousAt (fun x : α ↦ lowerLeftBlock (S x).L) x₀ ∧
      ContinuousAt (fun x : α ↦ (S x).D) x₀
  mem_nhdsWithin :
    {x : α |
      PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
        W B U₀ hU₀ Cedge r rEdge x} ∈
      nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)

set_option linter.unusedSectionVars false in
/-- Any chosen total-kernel complement gives the fixed-base canonical
product-difference local certificate. -/
theorem paperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate_of_isCompl
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
      W B U₀ hU₀ x₀ Cedge r rEdge where
  coefficientFields_centered_continuous :=
    paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_centered_continuousAt
      W B U₀ hU₀ Cedge hCedge hbase
  mem_nhdsWithin :=
    paperEndpointFixedBaseCanonicalProductDifferenceSourceRanks_selfBase_mem_nhdsWithin_source
      W B U₀ hU₀ Cedge r rEdge hCedge hbase

/-- A continuous reversed-edge family based at `B` admits a local canonical
product-difference certificate, relative to Aoyagi's source rank stratum, after
choosing endpoint bases from a total-kernel complement. -/
def PaperEndpointCanonicalProductDifferenceLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Prop :=
  ∃ U₀ : Submodule K (reverseVertex W 0),
    ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge

set_option linter.unusedSectionVars false in
/-- Finite-dimensional paper chains admit the local canonical product-difference
certificate near any continuous reversed-edge family based at the chain. -/
theorem exists_paperEndpointCanonicalProductDifferenceLocalCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p)) :
    PaperEndpointCanonicalProductDifferenceLocalCertificate W B x₀ Cedge r rEdge := by
  rcases exists_paperEndpointBasepointCertificate W B with ⟨U₀, hU₀, _⟩
  exact ⟨U₀, hU₀,
    paperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate_of_isCompl
      W B U₀ hU₀ Cedge r rEdge hCedge hbase⟩

/-- A fixed-base canonical product-difference local certificate together with
basepoint membership in Aoyagi's source-shaped rank stratum.

This makes the relative `nhdsWithin` package nonvacuous at the base chain when
the source product and edge ranks are supplied.  It still does not assert that
the source-rank stratum is open. -/
structure PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Prop where
  localCertificate :
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
      W B U₀ hU₀ x₀ Cedge r rEdge
  source_basepoint :
    x₀ ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge

set_option linter.unusedSectionVars false in
/-- A chosen total-kernel complement gives the canonical product-difference
local source certificate once the base chain's source rank data is supplied. -/
theorem paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank K (LinearMap.range (reverseEdge W B p)) = rEdge p)
    (hle : ∀ p : Fin N, r ≤ rEdge p) :
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
      W B U₀ hU₀ x₀ Cedge r rEdge where
  localCertificate :=
    paperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate_of_isCompl
      W B U₀ hU₀ Cedge r rEdge hCedge hbase
  source_basepoint :=
    paperEndpointFixedBaseSourceRankStratum_selfBase_mem
      (W := W) (B := B) hbase hprod hedge hle

set_option linter.unusedSectionVars false in
/-- A chosen total-kernel complement gives the canonical product-difference
local source certificate once the base product and edge rank equalities are
supplied.  The source inequalities are derived from the factorization of the
base product through each edge. -/
theorem paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl_of_rank_eq
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule K (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank K (LinearMap.range (reverseEdge W B p)) = rEdge p) :
    PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
      W B U₀ hU₀ x₀ Cedge r rEdge where
  localCertificate :=
    paperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate_of_isCompl
      W B U₀ hU₀ Cedge r rEdge hCedge hbase
  source_basepoint :=
    paperEndpointFixedBaseSourceRankStratum_selfBase_mem_of_rank_eq
      (W := W) (B := B) hbase hprod hedge

namespace PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

set_option linter.unusedSectionVars false in
/-- The local source certificate exposes an ordinary neighborhood whose
restriction to the source-shaped rank stratum satisfies the canonical
product-difference/source-rank conclusion. -/
theorem exists_source_neighborhood
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ}
    {r : ℕ} {rEdge : Fin N → ℕ}
    (cert :
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge) :
    ∃ U : Set α,
      U ∈ nhds x₀ ∧
      x₀ ∈ U ∧
      ∀ x, x ∈ U →
        x ∈ paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge →
          PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
            W B U₀ hU₀ Cedge r rEdge x := by
  rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
      cert.localCertificate.mem_nhdsWithin) with ⟨U, hU, hsubset⟩
  refine ⟨U, hU, mem_of_mem_nhds hU, ?_⟩
  intro x hxU hxsrc
  exact hsubset ⟨hxU, hxsrc⟩

end PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

/-- A continuous reversed-edge family based at `B` admits a canonical
product-difference local source certificate, after choosing endpoint bases from
a total-kernel complement and supplying the base source ranks. -/
def PaperEndpointCanonicalProductDifferenceLocalSourceCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α]
    (x₀ : α)
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ) : Prop :=
  ∃ U₀ : Submodule K (reverseVertex W 0),
    ∃ hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)),
      PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate
        W B U₀ hU₀ x₀ Cedge r rEdge

set_option linter.unusedSectionVars false in
/-- Finite-dimensional paper chains admit the canonical product-difference
local source certificate near a continuous reversed-edge family based at the
chain, when the base source ranks are supplied. -/
theorem exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank K (LinearMap.range (reverseEdge W B p)) = rEdge p)
    (hle : ∀ p : Fin N, r ≤ rEdge p) :
    PaperEndpointCanonicalProductDifferenceLocalSourceCertificate
      W B x₀ Cedge r rEdge := by
  rcases exists_paperEndpointBasepointCertificate W B with ⟨U₀, hU₀, _⟩
  exact ⟨U₀, hU₀,
    paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl
      W B U₀ hU₀ Cedge r rEdge hCedge hbase hprod hedge hle⟩

set_option linter.unusedSectionVars false in
/-- Finite-dimensional paper chains admit the canonical product-difference
local source certificate near a continuous reversed-edge family based at the
chain, when the base product and edge ranks are supplied.  The inequalities
`r ≤ rEdge p` are derived from the base chain. -/
theorem exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate_of_rank_eq
    [∀ j, FiniteDimensional K (W j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (Cedge : α → ∀ p : Fin N, reverseVertex W p.castSucc →L[K] reverseVertex W p.succ)
    (r : ℕ) (rEdge : Fin N → ℕ)
    (hCedge : ContinuousAt Cedge x₀)
    (hbase :
      Cedge x₀ = fun p : Fin N ↦ LinearMap.toContinuousLinearMap (reverseEdge W B p))
    (hprod :
      Module.finrank K (LinearMap.range (paperTotalMap W B)) = r)
    (hedge :
      ∀ p : Fin N,
        Module.finrank K (LinearMap.range (reverseEdge W B p)) = rEdge p) :
    PaperEndpointCanonicalProductDifferenceLocalSourceCertificate
      W B x₀ Cedge r rEdge := by
  rcases exists_paperEndpointBasepointCertificate W B with ⟨U₀, hU₀, _⟩
  exact ⟨U₀, hU₀,
    paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl_of_rank_eq
      W B U₀ hU₀ Cedge r rEdge hCedge hbase hprod hedge⟩

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
