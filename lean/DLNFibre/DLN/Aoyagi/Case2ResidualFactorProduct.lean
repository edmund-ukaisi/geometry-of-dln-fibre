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

end Aoyagi
end DLN
end DLNFibre
