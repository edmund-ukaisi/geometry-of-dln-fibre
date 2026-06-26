import DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct
import DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure

/-!
# Case 2 residual product to selected-entry chart bridge

This file composes the finite Case 2 residual-factor product bridge with the
center-indexed selected-entry chart-map vocabulary.  The displayed entrywise
readout remains an explicit hypothesis.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false in
/-- A supplied successor source-chart readout for Aoyagi's displayed Case 2
post-pivot product upgrades the two-edge residual-factor product to the
successor selected-entry center-coordinate chart matrix.

The entrywise readout, factor identities, and endpoint equivalences remain
hypotheses.  This theorem only composes the finite product bridge with the
definitional alignment between `case2DisplayedSourceChartMap` and
`SelectedEntrySignedBox.CenterCoord.chartMap`. -/
theorem residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
    {τ : Type*} {κ : Fin 3 → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) ℝ)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ (Fin.last 2))
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ (1 : Fin 3))
    (e₀κ : τ ≃ κ 0)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hD :
      (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) ℝ from
        by simpa using C (1 : Fin 2)).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ (1 : Fin 3)) (κ 0) ℝ from
        by simpa using C (0 : Fin 2)).submatrix e₁ e₀κ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
    (hentry :
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          case2DisplayedSourceChartMap n hS hnext
            (yNext (⟨(J + 2, J + 2),
              case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
              {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}))
            (SelectedEntrySignedBox.CenterCoord.sourceResidual yNext)
            ((case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) (Equiv.refl _) eNext (i, t)).1)) :
    ChartLocalSuffixState.residualFactorProduct C (Fin.last 2) 0
        (Fin.zero_le (Fin.last 2)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
          SelectedEntrySignedBox.CenterCoord.chartMap
            (⟨(J + 2, J + 2),
              case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
              {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)})
            yNext
            (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) e₂.symm (e₀κ.symm.trans eNext) c)) := by
  let pivotNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} :=
    ⟨(J + 2, J + 2),
      case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ≃
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) e₂.symm (e₀κ.symm.trans eNext)
  exact
    residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
      n hS hcont residual Cprime C
      (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext)
      residualCoordEquiv e₂ e₁ e₀κ hD hF
      (by
        intro i t
        have hp :
            residualCoordEquiv (e₂ i, e₀κ t) =
              case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
                n S (J + 1) (Equiv.refl _) eNext (i, t) := by
          apply Subtype.ext
          change
            ((e₂.symm (e₂ i)).1, (eNext (e₀κ.symm (e₀κ t))).1) =
              (i.1, (eNext t).1)
          rw [e₂.symm_apply_apply, e₀κ.symm_apply_apply]
        rw [hentry i t, hp]
        exact
          SelectedEntrySignedBox.CenterCoord.case2DisplayedSourceChartMap_eq_selectedEntrySignedBoxCenterCoord_chartMap_apply
            n hS hnext yNext
            (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) (Equiv.refl _) eNext (i, t)))

end Aoyagi
end DLN
end DLNFibre
