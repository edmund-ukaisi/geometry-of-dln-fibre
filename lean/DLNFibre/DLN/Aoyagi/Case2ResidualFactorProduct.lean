import DLNFibre.DLN.Aoyagi.ProductReduction
import DLNFibre.DLN.Aoyagi.BlowupArithmetic
import DLNFibre.DLN.Aoyagi.Case2ResidualIndex
import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates

/-!
# Case 2 residual-factor product bridge

This file connects the generic residual-factor product API to the displayed
Case 2 post-pivot two-factor product.  It is finite matrix reindexing only.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace Matrix

/-- A matrix equality can be checked after reindexing both axes by
equivalences. -/
theorem eq_of_submatrix_equiv_eq
    {ι ι' κ κ' R : Type*} (A B : Matrix ι' κ' R)
    (eι : ι ≃ ι') (eκ : κ ≃ κ')
    (h : A.submatrix eι eκ = B.submatrix eι eκ) :
    A = B := by
  ext i j
  simpa using congrFun (congrFun h (eι.symm i)) (eκ.symm j)

end Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The concrete three endpoints of the displayed Case 2 post-pivot two-edge
chain: free right endpoint, residual columns, then residual rows. -/
def case2PostPivotTwoEdgeDomain
    (n : ℕ → ℕ) (S J : ℕ) (τ : Type) : Fin 3 → Type :=
  Fin.cases τ
    (fun q : Fin 2 ↦
      Fin.cases (Case2ResidualColIndex n S (J + 1))
        (fun _ : Fin 1 ↦ Case2ResidualRowIndex n S (J + 1)) q)

instance case2PostPivotTwoEdgeDomain.fintype
    (n : ℕ → ℕ) (S J : ℕ) {τ : Type} [Fintype τ]
    (q : Fin 3) :
    Fintype (case2PostPivotTwoEdgeDomain n S J τ q) := by
  refine Fin.cases ?case0 ?caseSucc q
  · simpa [case2PostPivotTwoEdgeDomain] using (inferInstance : Fintype τ)
  · intro q
    refine Fin.cases ?case1 ?caseSucc2 q
    · simpa [case2PostPivotTwoEdgeDomain] using
        (inferInstance : Fintype (Case2ResidualColIndex n S (J + 1)))
    · intro q
      refine Fin.cases ?case2 ?caseSucc3 q
      · simpa [case2PostPivotTwoEdgeDomain] using
          (inferInstance : Fintype (Case2ResidualRowIndex n S (J + 1)))
      · intro q
        exact Fin.elim0 q

instance case2PostPivotTwoEdgeDomain.decidableEq
    (n : ℕ → ℕ) (S J : ℕ) {τ : Type} [DecidableEq τ]
    (q : Fin 3) :
    DecidableEq (case2PostPivotTwoEdgeDomain n S J τ q) := by
  refine Fin.cases ?case0 ?caseSucc q
  · simpa [case2PostPivotTwoEdgeDomain] using (inferInstance : DecidableEq τ)
  · intro q
    refine Fin.cases ?case1 ?caseSucc2 q
    · simpa [case2PostPivotTwoEdgeDomain] using
        (inferInstance : DecidableEq (Case2ResidualColIndex n S (J + 1)))
    · intro q
      refine Fin.cases ?case2 ?caseSucc3 q
      · simpa [case2PostPivotTwoEdgeDomain] using
          (inferInstance : DecidableEq (Case2ResidualRowIndex n S (J + 1)))
      · intro q
        exact Fin.elim0 q

/-- Cardinality equalities supply the endpoint equivalences used by Case 2
endpoint transport.

This is noncanonical finite reindexing only.  It does not preserve labels,
selected entries, chart membership, Jacobians, or analytic/RLCT content. -/
noncomputable def case2EndpointTransportEquivs_of_card_eq
    {τ : Type} [Fintype τ]
    {κ : Fin 3 → Type*} [∀ q, Fintype (κ q)]
    (n : ℕ → ℕ) (S J : ℕ)
    (hNext :
      Fintype.card τ =
        Fintype.card (Case2ResidualColIndex n S (J + 1)))
    (hEndpoints :
      ∀ q : Fin 3,
        Fintype.card (case2PostPivotTwoEdgeDomain n S J τ q) =
          Fintype.card (κ q)) :
    (τ ≃ Case2ResidualColIndex n S (J + 1)) ×
      (∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ q) := by
  classical
  exact ⟨Fintype.equivOfCardEq hNext,
    fun q ↦ Fintype.equivOfCardEq (hEndpoints q)⟩

universe u v

set_option linter.unusedSectionVars false in
/-- Source data and explicit scalar endpoint-size equalities give the pointwise
endpoint-cardinality hypotheses for the displayed Case 2 two-edge family.

This does not construct `τ`, prove the scalar size equalities, or make the
resulting endpoint equivalences canonical. -/
theorem case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module K (W₂ i)]
    [∀ i, ContinuousSMul K (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[K] W₂ i.castSucc)
    [∀ j, FiniteDimensional K (W₂ j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    {U₀ : Submodule K (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    {Cedge : α → ∀ p : Fin 2,
      reverseVertex W₂ p.castSucc →L[K] reverseVertex W₂ p.succ}
    {τ : Type} [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := K) W₂ B₂ U₀ hU₀ x₀ Cedge H r rEdge)
    (hTau : Fintype.card τ = H 3 - r)
    (hCol :
      Fintype.card (Case2ResidualColIndex n S (J + 1)) = H 2 - r)
    (hRow :
      Fintype.card (Case2ResidualRowIndex n S (J + 1)) = H 1 - r) :
    ∀ q : Fin 3,
      Fintype.card (case2PostPivotTwoEdgeDomain n S J τ q) =
        Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q) := by
  intro q
  have hEndpoint :=
    PaperEndpointFixedBaseRegularCoordinateSourceData.endpointComplementIndex_card_eq_H_rev_sub_rank
      (K := K) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
      (Cedge := Cedge) sourceData q
  fin_cases q
  · simpa [case2PostPivotTwoEdgeDomain] using hTau.trans hEndpoint.symm
  · change
      Fintype.card (Case2ResidualColIndex n S (J + 1)) =
        Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (1 : Fin 3))
    exact hCol.trans hEndpoint.symm
  · change
      Fintype.card (Case2ResidualRowIndex n S (J + 1)) =
        Fintype.card
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (2 : Fin 3))
    exact hRow.trans hEndpoint.symm

/-- The concrete two-factor family for the displayed Case 2 post-pivot lower
product: first the free `C'` tail, then the post-pivot residual block. -/
noncomputable def case2PostPivotFreeTwoEdgeFactorFamily
    {τ : Type} {R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    ∀ p : Fin 2,
      Matrix
        (case2PostPivotTwoEdgeDomain n S J τ p.succ)
        (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) R := by
  refine Fin.cases ?case0 ?caseSucc
  · simpa [case2PostPivotTwoEdgeDomain] using
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime
  · intro p
    refine Fin.cases ?case1 ?caseSucc2 p
    · simpa [case2PostPivotTwoEdgeDomain] using
        case2DisplayedPostPivotResidualBlock n hS hcont residual
    · intro p
      exact Fin.elim0 p

set_option linter.style.longLine false in
/-- A supplied two-edge residual-factor family gives Aoyagi's displayed Case 2
post-pivot free-`C'` product after explicit endpoint reindexing.

The equivalences and the two factor identities are hypotheses.  This theorem
does not construct the residual-factor family, identify it with a selected-entry
chart, prove source/image equality, or add analytic/RLCT content. -/
theorem case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix
    {τ R : Type*} [CommRing R]
    {κ : Fin 3 → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) R)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ (Fin.last 2))
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ (1 : Fin 3))
    (e₀ : τ ≃ κ 0)
    (hD :
      (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) R from
        by simpa using C (1 : Fin 2)).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ (1 : Fin 3)) (κ 0) R from
        by simpa using C (0 : Fin 2)).submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime) :
    (ChartLocalSuffixState.residualFactorProduct C (Fin.last 2) 0
        (Fin.zero_le (Fin.last 2))).submatrix e₂ e₀ =
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime := by
  let A : Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) R := by
    simpa using C (1 : Fin 2)
  let B : Matrix (κ (1 : Fin 3)) (κ 0) R := by
    simpa using C (0 : Fin 2)
  have hprod :
      ChartLocalSuffixState.residualFactorProduct C (Fin.last 2) 0
          (Fin.zero_le (Fin.last 2)) = A * B := by
    simpa [A, B] using
      ChartLocalSuffixState.residualFactorProduct_fin_two_eq_mul (K := R) C
  have hD' : A.submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual := by
    simpa [A] using hD
  have hF' : B.submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime := by
    simpa [B] using hF
  calc
    (ChartLocalSuffixState.residualFactorProduct C (Fin.last 2) 0
        (Fin.zero_le (Fin.last 2))).submatrix e₂ e₀ =
        (A * B).submatrix e₂ e₀ := by rw [hprod]
    _ = A.submatrix e₂ e₁ * B.submatrix e₁ e₀ := by
      exact (Matrix.submatrix_mul_equiv A B e₂ e₁ e₀).symm
    _ = case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime := by
      rw [hD', hF']
      rfl

set_option linter.style.longLine false in
/-- An adjacent two-edge window in a longer supplied residual-factor family
gives Aoyagi's displayed Case 2 post-pivot free-`C'` product after explicit
endpoint reindexing.

The endpoint equivalences and the two factor identities are hypotheses.  This
theorem does not identify a full retained-passive suffix with this adjacent
window, construct the endpoint equivalences, or add selected-entry/source
chart content. -/
theorem case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_adjacent_two_submatrix
    {τ R : Type*} [CommRing R]
    {N : ℕ} {κ : Fin (N + 3) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) R)
    (p : Fin (N + 1))
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ p.succ.succ)
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ p.succ.castSucc)
    (e₀ : τ ≃ κ p.castSucc.castSucc)
    (hD :
      (show Matrix (κ p.succ.succ) (κ p.succ.castSucc) R from
        by simpa using C p.succ).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ p.succ.castSucc) (κ p.castSucc.castSucc) R from
        by simpa using C p.castSucc).submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime) :
    (ChartLocalSuffixState.residualFactorProduct C
        p.succ.succ p.castSucc.castSucc
        ((Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ p)).trans
          (Fin.castSucc_le_succ p.succ))).submatrix e₂ e₀ =
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime := by
  calc
    (ChartLocalSuffixState.residualFactorProduct C
        p.succ.succ p.castSucc.castSucc
        ((Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ p)).trans
          (Fin.castSucc_le_succ p.succ))).submatrix e₂ e₀ =
        (show Matrix (κ p.succ.succ) (κ p.succ.castSucc) R from
          by simpa using C p.succ).submatrix e₂ e₁ *
        (show Matrix (κ p.succ.castSucc) (κ p.castSucc.castSucc) R from
          by simpa using C p.castSucc).submatrix e₁ e₀ := by
      exact
        ChartLocalSuffixState.residualFactorProduct_adjacent_two_submatrix_eq_mul
          (K := R) C p e₂ e₁ e₀
    _ = case2DisplayedPostPivotResidualBlock n hS hcont residual *
        case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime := by
      rw [hD, hF]
    _ = case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime := rfl

set_option linter.style.longLine false in
/-- The concrete displayed Case 2 two-edge factor family unfolds to the
displayed post-pivot free-`C'` product.

This removes only generic endpoint-family and factor-identity boilerplate; it
does not construct successor chart coordinates or an entrywise selected-center
readout. -/
theorem residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_freeTwoEdgeFactorProduct
    {τ : Type} {R : Type*} [CommRing R] [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    ChartLocalSuffixState.residualFactorProduct
        (case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual Cprime)
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime := by
  simpa [case2PostPivotFreeTwoEdgeFactorFamily, case2PostPivotTwoEdgeDomain] using
    case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix
      n hS hcont residual Cprime
      (case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual Cprime)
      (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      (by
        ext i j
        rfl)
      (by
        ext i t
        rfl)

set_option linter.style.longLine false in
/-- For Aoyagi's paper `C' = Q⁻¹ C`, the concrete displayed Case 2 two-edge
factor product is the source residual block at `(S,J+1)` times the
formula-level successor following factor restricted to that next residual
domain.

This is finite product-reduction algebra only.  It does not construct
successor source data, selected-entry readout, chart coverage, normal
crossings, pole order, or RLCT content. -/
theorem residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_paperCprime_eq_sourceResidualBlock_successorFollowingFactor
    {τ : Type} {R : Type*} [CommRing R] [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    ChartLocalSuffixState.residualFactorProduct
        (case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual
          (case2DisplayedPaperCprime n hS hcont residual C))
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
      case2SourceResidualBlock (n := n) (S := S) (J := J + 1)
          (case2DisplayedPostPivotSourceResidual n hS hcont residual) *
        case2SourceFollowingFactor (n := n) (S := S) (J := J + 1)
          (Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceSuccessorFollowingFactor
            n hS hcont residual C) := by
  rw [residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_freeTwoEdgeFactorProduct]
  rw [case2DisplayedPostPivotFreeTwoEdgeFactorProduct]
  rw [← case2SourceResidualBlock_postPivotSourceResidual n hS hcont residual]
  rw [Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPostPivotFreeFollowingFactor_paperCprime_eq_sourceFollowingFactor_succ]
  rw [Case2DisplayedSuppliedChartFamilyBoundary.case2SourceFollowingFactor_successorFollowingFactor_succ]

set_option linter.style.longLine false in
/-- Entrywise expansion of Aoyagi's displayed Case 2 post-pivot lower product
`D_(J+1) * C'_+`.

This is just the finite matrix-product formula for the displayed product on
the continuing `(S,J+1)` domains.  It does not identify the entries with
selected-entry center coordinates or source-chart coordinates. -/
theorem case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (i : Case2ResidualRowIndex n S (J + 1)) (t : τ) :
    case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
      ∑ j : Case2ResidualColIndex n S (J + 1),
        case2DisplayedPostPivotResidualBlock n hS hcont residual i j *
          case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime j t := by
  simp [case2DisplayedPostPivotFreeTwoEdgeFactorProduct, Matrix.mul_apply]

set_option linter.style.longLine false in
/-- Entrywise expansion of Aoyagi's displayed Case 2 post-pivot lower product
directly in terms of the free pivot-first `C'` tail.

This is the same finite matrix-product formula as
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply`, with the reindexed
following-factor tail unfolded. -/
theorem case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply_eq_sum_freeCprime
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (i : Case2ResidualRowIndex n S (J + 1)) (t : τ) :
    case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
      ∑ j : Case2ResidualColIndex n S (J + 1),
        case2DisplayedPostPivotResidualBlock n hS hcont residual i j *
          Cprime
            (Sum.inr
              ((case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont).symm j)) t := by
  simp [case2DisplayedPostPivotFreeTwoEdgeFactorProduct,
    case2DisplayedPostPivotFreeFollowingFactor, case2DisplayedFreeCprimeTail, Matrix.mul_apply]

set_option linter.style.longLine false in
/-- Zero-extend a prescribed Case 2 residual block to source-coordinate
residual data.

This is finite source-coordinate bookkeeping only.  It is not chart production,
coverage, a transition invariant, normal crossings, pole order, or RLCT
content. -/
noncomputable def case2SourceResidualBlockExtension
    {R : Type*} [Zero R]
    (n : ℕ → ℕ) {S J : ℕ}
    (D : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R) :
    ℕ × ℕ → R :=
  fun p ↦
    if hi : p.1 ∈ case2ResidualBlockRows n S J then
      if hj : p.2 ∈ case2ResidualBlockCols n S J then
        D ⟨p.1, hi⟩ ⟨p.2, hj⟩
      else 0
    else 0

/-- Restricting the zero extension to its residual block recovers the
prescribed matrix. -/
theorem case2SourceResidualBlock_extension
    {R : Type*} [Zero R]
    (n : ℕ → ℕ) {S J : ℕ}
    (D : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R) :
    case2SourceResidualBlock (n := n) (S := S) (J := J)
        (case2SourceResidualBlockExtension n D) = D := by
  ext i j
  simp [case2SourceResidualBlock, case2SourceResidualBlockExtension]

set_option linter.style.longLine false in
/-- The successor-block zero extension realizes any prescribed post-pivot
Schur block in the displayed Case 2 calculation.

The construction sets the old displayed pivot row and column to zero off the
pivot and reads the supplied matrix on the lower-right successor block.  This
is finite constructed-data algebra only; it is not a theorem about an arbitrary
retained-passive source/readback point. -/
theorem case2DisplayedPostPivotResidualBlock_sourceResidualBlockExtension
    {R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (D :
      Matrix (Case2ResidualRowIndex n S (J + 1))
        (Case2ResidualColIndex n S (J + 1)) R) :
    case2DisplayedPostPivotResidualBlock n hS hcont
        (case2SourceResidualBlockExtension (n := n) (S := S) (J := J + 1) D) =
      D := by
  ext i j
  let er := case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont
  let ec := case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont
  let residual :=
    case2SourceResidualBlockExtension (n := n) (S := S) (J := J + 1) D
  let A := case2DisplayedPaperDchart n hS hcont residual
  have hi_succ : i.1 ∈ case2ResidualBlockRows n S (J + 1) := i.2
  have hj_succ : j.1 ∈ case2ResidualBlockCols n S (J + 1) := j.2
  have hi_ge : J + 2 ≤ i.1 := ((mem_case2ResidualBlockRows n S (J + 1) i.1).mp i.2).1
  have hj_ge : J + 2 ≤ j.1 := ((mem_case2ResidualBlockCols n S (J + 1) j.1).mp j.2).1
  have hi_ne_pivot : i.1 ≠ J + 1 := by omega
  have hj_ne_pivot : j.1 ≠ J + 1 := by omega
  have hD_entry :
      A (er.symm i).1 (ec.symm j).1 = D i j := by
    simp [A, residual, case2DisplayedPaperDchart,
      case2DisplayedSourceNormalizedBlock, case2DisplayedSourceNormalizedMap,
      selectedEntryNormalizedMap, case2SourceResidualBlockExtension,
      hi_ne_pivot, hi_succ, hj_succ, er, ec]
  have hleft_zero :
      A (er.symm i).1 (case2DisplayedPivotCol n hS hcont) = 0 := by
    simp [A, residual, case2DisplayedPaperDchart,
      case2DisplayedSourceNormalizedBlock, case2DisplayedSourceNormalizedMap,
      selectedEntryNormalizedMap, case2SourceResidualBlockExtension,
      hi_ne_pivot, case2DisplayedPivotCol, er]
  have htop_zero :
      A (case2DisplayedPivotRow n hS hcont) (ec.symm j).1 = 0 := by
    simp [A, residual, case2DisplayedPaperDchart,
      case2DisplayedSourceNormalizedBlock, case2DisplayedSourceNormalizedMap,
      selectedEntryNormalizedMap, case2SourceResidualBlockExtension,
      hj_ne_pivot, case2DisplayedPivotRow, ec]
  rw [case2DisplayedPostPivotResidualBlock]
  change
    (pivotFirstD (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont) A -
        pivotFirstX (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont) A *
          pivotFirstY (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont) A)
        (er.symm i) (ec.symm j) = D i j
  rw [pivotFirstSchurComplement_apply]
  rw [hD_entry, hleft_zero, htop_zero]
  simp

set_option linter.style.longLine false in
/-- A free pivot-first `C'` whose post-pivot following-factor tail is the
prescribed successor following matrix.

The top row is set to zero because it is ignored by
`case2DisplayedPostPivotFreeFollowingFactor`. -/
noncomputable def case2DisplayedPostPivotFreeCprimeOfFollowingFactor
    {τ R : Type*} [Zero R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (F : Matrix (Case2ResidualColIndex n S (J + 1)) τ R) :
    Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  fun i t ↦
    match i with
    | Sum.inl _ => 0
    | Sum.inr j =>
        F (case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont j) t

/-- The free `C'` constructor realizes the prescribed post-pivot following
factor. -/
theorem case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor
    {τ R : Type*} [Zero R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (F : Matrix (Case2ResidualColIndex n S (J + 1)) τ R) :
    case2DisplayedPostPivotFreeFollowingFactor n hS hcont
        (case2DisplayedPostPivotFreeCprimeOfFollowingFactor n hS hcont F) =
      F := by
  ext j t
  simp [case2DisplayedPostPivotFreeFollowingFactor,
    case2DisplayedFreeCprimeTail,
    case2DisplayedPostPivotFreeCprimeOfFollowingFactor]

set_option linter.style.longLine false in
/-- Multiplying a matrix reindexed on the right by the matching reindexed
identity recovers the original matrix. -/
theorem Matrix.submatrix_id_equiv_symm_mul_one_submatrix_id_equiv
    {ι κ τ R : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι τ R) (e : τ ≃ κ) :
    M.submatrix id e.symm *
        ((1 : Matrix κ κ R).submatrix id e) =
      M := by
  ext i t
  rw [Matrix.mul_apply]
  classical
  calc
    (∑ j : κ, M i (e.symm j) * (1 : Matrix κ κ R) j (e t)) =
        M i (e.symm (e t)) * (1 : Matrix κ κ R) (e t) (e t) := by
      exact Finset.sum_eq_single (e t)
        (by
          intro b _ hb
          simp [hb])
        (by
          intro hmissing
          exact False.elim (hmissing (Finset.mem_univ (e t))))
    _ = M i t := by
      simp

set_option linter.style.longLine false in
/-- Source residual data obtained by zero-extending a target successor residual
matrix after reindexing its right endpoint to successor residual columns. -/
noncomputable def case2DisplayedPostPivotSourceResidualOfMatrix
    {τ R : Type*} [Zero R]
    (n : ℕ → ℕ) {S J : ℕ}
    (M : Matrix (Case2ResidualRowIndex n S (J + 1)) τ R)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    ℕ × ℕ → R :=
  let D : Matrix (Case2ResidualRowIndex n S (J + 1))
      (Case2ResidualColIndex n S (J + 1)) R :=
    M.submatrix id eNext.symm
  case2SourceResidualBlockExtension (n := n) (S := S) (J := J + 1) D

set_option linter.style.longLine false in
/-- Free `Cprime` data whose post-pivot following-factor tail is the
reindexed identity on successor residual columns. -/
noncomputable def case2DisplayedPostPivotFreeCprimeOfMatrix
    {τ R : Type*} [Zero R] [One R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (_M : Matrix (Case2ResidualRowIndex n S (J + 1)) τ R)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  let F :
      Matrix (Case2ResidualColIndex n S (J + 1)) τ R :=
    (1 : Matrix
      (Case2ResidualColIndex n S (J + 1))
      (Case2ResidualColIndex n S (J + 1)) R).submatrix id eNext
  case2DisplayedPostPivotFreeCprimeOfFollowingFactor n hS hcont F

set_option linter.style.longLine false in
/-- The explicit zero-extension residual and reindexed-identity `Cprime`
realize the prescribed successor matrix as the displayed Case 2 post-pivot
free two-edge product. -/
theorem case2DisplayedPostPivotFreeTwoEdgeFactorProduct_sourceResidualOfMatrix_freeCprimeOfMatrix
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (M : Matrix (Case2ResidualRowIndex n S (J + 1)) τ R)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont
        (case2DisplayedPostPivotSourceResidualOfMatrix n M eNext)
        (case2DisplayedPostPivotFreeCprimeOfMatrix n hS hcont M eNext) =
      M := by
  rw [case2DisplayedPostPivotFreeTwoEdgeFactorProduct]
  rw [case2DisplayedPostPivotSourceResidualOfMatrix]
  rw [case2DisplayedPostPivotResidualBlock_sourceResidualBlockExtension]
  rw [case2DisplayedPostPivotFreeCprimeOfMatrix]
  rw [case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor]
  exact Matrix.submatrix_id_equiv_symm_mul_one_submatrix_id_equiv M eNext

set_option linter.style.longLine false in
/-- Any matrix whose right endpoint is equivalent to the successor residual
column domain can be realized as a constructed displayed Case 2 post-pivot
free two-edge product.

The residual block is chosen to be the target matrix with its right endpoint
reindexed to successor columns, and the following factor is the matching
reindexed identity.  This is constructed finite data, not an arbitrary
retained-passive readback statement. -/
theorem exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_matrix_of_colEquiv
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (M : Matrix (Case2ResidualRowIndex n S (J + 1)) τ R)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    ∃ residual : ℕ × ℕ → R,
    ∃ Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R,
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime = M := by
  let D : Matrix (Case2ResidualRowIndex n S (J + 1))
      (Case2ResidualColIndex n S (J + 1)) R :=
    M.submatrix id eNext.symm
  let residual : ℕ × ℕ → R :=
    case2SourceResidualBlockExtension (n := n) (S := S) (J := J + 1) D
  let F :
      Matrix (Case2ResidualColIndex n S (J + 1)) τ R :=
    (1 : Matrix
      (Case2ResidualColIndex n S (J + 1))
      (Case2ResidualColIndex n S (J + 1)) R).submatrix id eNext
  let Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
    case2DisplayedPostPivotFreeCprimeOfFollowingFactor n hS hcont F
  refine ⟨residual, Cprime, ?_⟩
  rw [case2DisplayedPostPivotFreeTwoEdgeFactorProduct]
  rw [case2DisplayedPostPivotResidualBlock_sourceResidualBlockExtension]
  rw [case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor]
  exact Matrix.submatrix_id_equiv_symm_mul_one_submatrix_id_equiv M eNext

set_option linter.style.longLine false in
/-- Entrywise selected-center readout gives the displayed Case 2 post-pivot
product as the selected-center coordinate matrix after endpoint reindexing.

This is finite matrix extensionality only.  It does not prove the entrywise
readout, construct the endpoint equivalences, or produce the source/chart
data. -/
theorem case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_centerCoordinateSubmatrix_of_entrywise
    {τ R : Type*} [CommRing R]
    {κ₂ κ₀ : Type*}
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    {ι : Type*} {center : Finset ι}
    (centerCoord : center → R)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex κ₂ κ₀ ≃ center)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ₂)
    (e₀ : τ ≃ κ₀)
    (hentry :
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          centerCoord (residualCoordEquiv (e₂ i, e₀ t))) :
    case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime =
      (AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex κ₂ κ₀ ↦
          centerCoord (residualCoordEquiv c))).submatrix e₂ e₀ := by
  ext i t
  simpa [AoyagiResidualBlockCoordinateIndex.matrix] using hentry i t

set_option linter.style.longLine false in
/-- Entrywise readout into the successor Case 2 source-chart map gives a
matrix identity on the post-pivot displayed product.

This is a finite endpoint-reindexing bridge only.  The entrywise readout,
successor source coordinates, and column endpoint equivalence are still
hypotheses; the theorem does not construct them or identify them with a
selected-entry center-coordinate chart. -/
theorem case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSourceChartMapMatrix_of_entrywise
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (uNext : R) (residualNext : ℕ × ℕ → R)
    (e₀ : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hentry :
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          case2DisplayedSourceChartMap n hS hnext uNext residualNext
            ((case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) (Equiv.refl _) e₀ (i, t)).1)) :
    case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex
            (Case2ResidualRowIndex n S (J + 1)) τ ↦
          case2DisplayedSourceChartMap n hS hnext uNext residualNext
            ((case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) (Equiv.refl _) e₀ c).1)) := by
  ext i t
  simpa [AoyagiResidualBlockCoordinateIndex.matrix] using hentry i t

set_option linter.style.longLine false in
/-- A displayed Case 2 post-pivot product identity upgrades the reindexed
two-edge residual-factor product to an exact selected-center coordinate matrix.

The displayed right-hand side is still a hypothesis.  This theorem only
removes the final equivalence-submatrix wrapper. -/
theorem residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_submatrix
    {τ R : Type*} [CommRing R]
    {κ : Fin 3 → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) R)
    {ι : Type*} {center : Finset ι}
    (centerCoord : center → R)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ≃ center)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ (Fin.last 2))
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ (1 : Fin 3))
    (e₀ : τ ≃ κ 0)
    (hD :
      (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) R from
        by simpa using C (1 : Fin 2)).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ (1 : Fin 3)) (κ 0) R from
        by simpa using C (0 : Fin 2)).submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
    (hRHS :
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime =
        (AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
            centerCoord (residualCoordEquiv c))).submatrix e₂ e₀) :
    ChartLocalSuffixState.residualFactorProduct C (Fin.last 2) 0
        (Fin.zero_le (Fin.last 2)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
          centerCoord (residualCoordEquiv c)) := by
  apply Matrix.eq_of_submatrix_equiv_eq
    (ChartLocalSuffixState.residualFactorProduct C (Fin.last 2) 0
      (Fin.zero_le (Fin.last 2)))
    (AoyagiResidualBlockCoordinateIndex.matrix
      (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
        centerCoord (residualCoordEquiv c)))
    e₂ e₀
  calc
    (ChartLocalSuffixState.residualFactorProduct C (Fin.last 2) 0
        (Fin.zero_le (Fin.last 2))).submatrix e₂ e₀ =
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime := by
      exact
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix
          n hS hcont residual Cprime C e₂ e₁ e₀ hD hF
    _ =
        (AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
            centerCoord (residualCoordEquiv c))).submatrix e₂ e₀ := hRHS

set_option linter.style.longLine false in
/-- Entrywise selected-center readout for the displayed Case 2 post-pivot
product upgrades the unreindexed two-edge residual-factor product to the exact
selected-center coordinate matrix.

The entrywise readout, factor identities, and endpoint equivalences remain
hypotheses.  This theorem only composes the finite displayed-product bridge
with matrix extensionality. -/
theorem residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
    {τ R : Type*} [CommRing R]
    {κ : Fin 3 → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) R)
    {ι : Type*} {center : Finset ι}
    (centerCoord : center → R)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ≃ center)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ (Fin.last 2))
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ (1 : Fin 3))
    (e₀ : τ ≃ κ 0)
    (hD :
      (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) R from
        by simpa using C (1 : Fin 2)).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ (1 : Fin 3)) (κ 0) R from
        by simpa using C (0 : Fin 2)).submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
    (hentry :
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          centerCoord (residualCoordEquiv (e₂ i, e₀ t))) :
    ChartLocalSuffixState.residualFactorProduct C (Fin.last 2) 0
        (Fin.zero_le (Fin.last 2)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
          centerCoord (residualCoordEquiv c)) := by
  exact
    residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_submatrix
      n hS hcont residual Cprime C centerCoord residualCoordEquiv e₂ e₁ e₀ hD hF
      (case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_centerCoordinateSubmatrix_of_entrywise
        n hS hcont residual Cprime centerCoord residualCoordEquiv e₂ e₀ hentry)

set_option linter.style.longLine false in
/-- Entrywise selected-center readout for the displayed Case 2 post-pivot
product upgrades an adjacent two-edge residual-factor product in a longer
family to the exact selected-center coordinate matrix.

The endpoint equivalences, factor identities, and entrywise readout remain
hypotheses.  This theorem only composes the generic adjacent-window transport
with finite Case 2 matrix extensionality. -/
theorem residualFactorProduct_adjacent_two_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
    {τ R : Type*} [CommRing R]
    {N : ℕ} {κ : Fin (N + 3) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) R)
    (p : Fin (N + 1))
    {ι : Type*} {center : Finset ι}
    (centerCoord : center → R)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ p.succ.succ) (κ p.castSucc.castSucc) ≃ center)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ p.succ.succ)
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ p.succ.castSucc)
    (e₀ : τ ≃ κ p.castSucc.castSucc)
    (hD :
      (show Matrix (κ p.succ.succ) (κ p.succ.castSucc) R from
        by simpa using C p.succ).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ p.succ.castSucc) (κ p.castSucc.castSucc) R from
        by simpa using C p.castSucc).submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
    (hentry :
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          centerCoord (residualCoordEquiv (e₂ i, e₀ t))) :
    ChartLocalSuffixState.residualFactorProduct C
        p.succ.succ p.castSucc.castSucc
        ((Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ p)).trans
          (Fin.castSucc_le_succ p.succ)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex
            (κ p.succ.succ) (κ p.castSucc.castSucc) ↦
          centerCoord (residualCoordEquiv c)) := by
  apply Matrix.eq_of_submatrix_equiv_eq
    (ChartLocalSuffixState.residualFactorProduct C
      p.succ.succ p.castSucc.castSucc
      ((Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ p)).trans
        (Fin.castSucc_le_succ p.succ)))
    (AoyagiResidualBlockCoordinateIndex.matrix
      (fun c : AoyagiResidualBlockCoordinateIndex
          (κ p.succ.succ) (κ p.castSucc.castSucc) ↦
        centerCoord (residualCoordEquiv c)))
    e₂ e₀
  calc
    (ChartLocalSuffixState.residualFactorProduct C
        p.succ.succ p.castSucc.castSucc
        ((Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ p)).trans
          (Fin.castSucc_le_succ p.succ))).submatrix e₂ e₀ =
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime := by
      exact
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_adjacent_two_submatrix
          n hS hcont residual Cprime C p e₂ e₁ e₀ hD hF
    _ =
        (AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex
              (κ p.succ.succ) (κ p.castSucc.castSucc) ↦
            centerCoord (residualCoordEquiv c))).submatrix e₂ e₀ :=
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_centerCoordinateSubmatrix_of_entrywise
        n hS hcont residual Cprime centerCoord residualCoordEquiv e₂ e₀ hentry

end Aoyagi
end DLN
end DLNFibre
