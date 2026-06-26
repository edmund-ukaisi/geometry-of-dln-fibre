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

set_option linter.style.longLine false in
/-- The concrete displayed Case 2 two-edge factor family upgrades to the
successor selected-entry center-coordinate chart matrix from the supplied
entrywise successor readout.

This specializes
`residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise`
to the concrete endpoint family
`tau -> Case2ResidualColIndex -> Case2ResidualRowIndex`, removing the generic
factor-family and endpoint-equivalence hypotheses.  The entrywise successor
readout remains a hypothesis. -/
theorem residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
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
    ChartLocalSuffixState.residualFactorProduct
        (case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual Cprime)
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex
            (Case2ResidualRowIndex n S (J + 1)) τ ↦
          SelectedEntrySignedBox.CenterCoord.chartMap
            (⟨(J + 2, J + 2),
              case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
              {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)})
            yNext
            (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) (Equiv.refl _) eNext c)) := by
  simpa [case2PostPivotFreeTwoEdgeFactorFamily, case2PostPivotTwoEdgeDomain] using
    residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
      (τ := τ) (κ := case2PostPivotTwoEdgeDomain n S J τ)
      n hS hcont hnext residual Cprime
      (case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual Cprime)
      yNext
      (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) eNext
      (by
        ext i j
        rfl)
      (by
        ext i t
        rfl)
      hentry

set_option linter.style.longLine false in
/-- A fixed nonzero successor pivot produces successor selected-entry
coordinates for the displayed Case 2 post-pivot product.

This is the fixed-pivot inverse for the selected-entry chart, specialized to
the successor `(S, J + 1)` residual center.  It does not prove the pivot is
nonzero and does not construct a full source chart. -/
theorem exists_successorSourceChartMap_entrywise_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero
    {τ : Type*}
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hpivot :
      let pivotNext :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} :=
        ⟨(J + 2, J + 2),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩
      let residualCoordEquiv :
          AoyagiResidualBlockCoordinateIndex
              (Case2ResidualRowIndex n S (J + 1)) τ ≃
            (case2ResidualBlockPivotEntries n S (J + 1) : Type) :=
        case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
          n S (J + 1) (Equiv.refl _) eNext
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
        (residualCoordEquiv.symm pivotNext).1
        (residualCoordEquiv.symm pivotNext).2 ≠ 0) :
    ∃ yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ,
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          case2DisplayedSourceChartMap n hS hnext
            (yNext (⟨(J + 2, J + 2),
              case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
              {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}))
            (SelectedEntrySignedBox.CenterCoord.sourceResidual yNext)
            ((case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) (Equiv.refl _) eNext (i, t)).1) := by
  let pivotNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} :=
    ⟨(J + 2, J + 2),
      case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (Case2ResidualRowIndex n S (J + 1)) τ ≃
        (case2ResidualBlockPivotEntries n S (J + 1) : Type) :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (Equiv.refl _) eNext
  let value :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ :=
    fun p ↦
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
        (residualCoordEquiv.symm p).1
        (residualCoordEquiv.symm p).2
  have hpivot_value : value pivotNext ≠ 0 := by
    simpa [value, pivotNext, residualCoordEquiv] using hpivot
  rcases
    SelectedEntrySignedBox.CenterCoord.exists_chartMap_eq_value_of_pivot_ne_zero
      pivotNext value hpivot_value with
    ⟨yNext, hyNext⟩
  refine ⟨yNext, ?_⟩
  intro i t
  let c : AoyagiResidualBlockCoordinateIndex
      (Case2ResidualRowIndex n S (J + 1)) τ := (i, t)
  have hvalue :
      value (residualCoordEquiv c) =
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t := by
    simp [value, residualCoordEquiv, c]
  calc
    case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
        value (residualCoordEquiv c) := hvalue.symm
    _ = SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
          (residualCoordEquiv c) := by
        exact (congrFun hyNext (residualCoordEquiv c)).symm
    _ = case2DisplayedSourceChartMap n hS hnext
          (yNext (⟨(J + 2, J + 2),
            case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
            {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}))
          (SelectedEntrySignedBox.CenterCoord.sourceResidual yNext)
          ((case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
            n S (J + 1) (Equiv.refl _) eNext (i, t)).1) := by
        simpa [pivotNext, residualCoordEquiv, c] using
          (SelectedEntrySignedBox.CenterCoord.case2DisplayedSourceChartMap_eq_selectedEntrySignedBoxCenterCoord_chartMap_apply
            n hS hnext yNext (residualCoordEquiv c)).symm

end Aoyagi
end DLN
end DLNFibre
