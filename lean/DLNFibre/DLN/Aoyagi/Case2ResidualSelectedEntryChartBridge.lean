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
/-- A supplied successor source-chart readout for Aoyagi's displayed Case 2
post-pivot product upgrades an adjacent two-edge window in a longer supplied
residual-factor family to the successor selected-entry center-coordinate chart
matrix.

The endpoint equivalences, factor identities, and entrywise readout remain
hypotheses.  This theorem only composes the generic adjacent-window product
transport with the selected-entry chart-map vocabulary. -/
theorem residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
    {τ : Type*} {N : ℕ} {κ : Fin (N + 3) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) ℝ)
    (p : Fin (N + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ p.succ.succ)
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ p.succ.castSucc)
    (e₀κ : τ ≃ κ p.castSucc.castSucc)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hD :
      (show Matrix (κ p.succ.succ) (κ p.succ.castSucc) ℝ from
        by simpa using C p.succ).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ p.succ.castSucc) (κ p.castSucc.castSucc) ℝ from
        by simpa using C p.castSucc).submatrix e₁ e₀κ =
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
    ChartLocalSuffixState.residualFactorProduct C
        p.succ.succ p.castSucc.castSucc
        ((Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ p)).trans
          (Fin.castSucc_le_succ p.succ)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex
            (κ p.succ.succ) (κ p.castSucc.castSucc) ↦
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
      AoyagiResidualBlockCoordinateIndex
          (κ p.succ.succ) (κ p.castSucc.castSucc) ≃
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) e₂.symm (e₀κ.symm.trans eNext)
  exact
    residualFactorProduct_adjacent_two_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
      n hS hcont residual Cprime C p
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
/-- A full residual-factor product through a supplied adjacent Case 2 window
has the successor selected-entry matrix as its middle factor, with the outside
factors left explicit.

The endpoint equivalences, factor identities, and entrywise readout remain
hypotheses.  This theorem does not assert that the outside factors are
identities, invertible, or analytically harmless. -/
theorem residualFactorProduct_split_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
    {τ : Type*} {N : ℕ} {κ : Fin (N + 3) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) ℝ)
    {i j : Fin (N + 3)} (p : Fin (N + 1))
    (hi : i ≤ p.castSucc.castSucc) (hj : p.succ.succ ≤ j)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ p.succ.succ)
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ p.succ.castSucc)
    (e₀κ : τ ≃ κ p.castSucc.castSucc)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hD :
      (show Matrix (κ p.succ.succ) (κ p.succ.castSucc) ℝ from
        by simpa using C p.succ).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ p.succ.castSucc) (κ p.castSucc.castSucc) ℝ from
        by simpa using C p.castSucc).submatrix e₁ e₀κ =
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
    ChartLocalSuffixState.residualFactorProduct C j i
        (hi.trans (((Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ p)).trans
          (Fin.castSucc_le_succ p.succ)).trans hj)) =
      ChartLocalSuffixState.residualFactorProduct C j p.succ.succ hj *
        (AoyagiResidualBlockCoordinateIndex.matrix
            (fun c : AoyagiResidualBlockCoordinateIndex
                (κ p.succ.succ) (κ p.castSucc.castSucc) ↦
              SelectedEntrySignedBox.CenterCoord.chartMap
                (⟨(J + 2, J + 2),
                  case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
                  {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)})
                yNext
                (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
                  n S (J + 1) e₂.symm (e₀κ.symm.trans eNext) c)) *
          ChartLocalSuffixState.residualFactorProduct C p.castSucc.castSucc i hi) := by
  let M : Matrix (κ p.succ.succ) (κ p.castSucc.castSucc) ℝ :=
    AoyagiResidualBlockCoordinateIndex.matrix
      (fun c : AoyagiResidualBlockCoordinateIndex
          (κ p.succ.succ) (κ p.castSucc.castSucc) ↦
        SelectedEntrySignedBox.CenterCoord.chartMap
          (⟨(J + 2, J + 2),
            case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
            {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)})
          yNext
          (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
            n S (J + 1) e₂.symm (e₀κ.symm.trans eNext) c))
  have hmiddle :
      ChartLocalSuffixState.residualFactorProduct C
          p.succ.succ p.castSucc.castSucc
          ((Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ p)).trans
            (Fin.castSucc_le_succ p.succ)) = M := by
    simpa [M] using
      residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
        n hS hcont hnext residual Cprime C p yNext e₂ e₁ e₀κ eNext hD hF hentry
  exact
    ChartLocalSuffixState.residualFactorProduct_split_adjacent_two_of_middle_eq
      (K := ℝ) C p hi hj M hmiddle

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

set_option linter.style.longLine false in
/-- If the displayed post-pivot product has nonzero successor pivot, an
adjacent two-edge window in a longer supplied residual-factor family admits
successor selected-entry coordinates whose center-coordinate matrix is that
adjacent residual-factor product.

The fixed-pivot nonzero hypothesis is still supplied.  The endpoint
equivalences and two factor identities for the adjacent window are also still
supplied.  This theorem does not identify a full retained-passive suffix with
the adjacent window. -/
theorem exists_residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero
    {τ : Type*} {N : ℕ} {κ : Fin (N + 3) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) ℝ)
    (p : Fin (N + 1))
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ p.succ.succ)
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ p.succ.castSucc)
    (e₀κ : τ ≃ κ p.castSucc.castSucc)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hD :
      (show Matrix (κ p.succ.succ) (κ p.succ.castSucc) ℝ from
        by simpa using C p.succ).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ p.succ.castSucc) (κ p.castSucc.castSucc) ℝ from
        by simpa using C p.castSucc).submatrix e₁ e₀κ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
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
      ChartLocalSuffixState.residualFactorProduct C
          p.succ.succ p.castSucc.castSucc
          ((Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ p)).trans
            (Fin.castSucc_le_succ p.succ)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex
              (κ p.succ.succ) (κ p.castSucc.castSucc) ↦
            SelectedEntrySignedBox.CenterCoord.chartMap
              (⟨(J + 2, J + 2),
                case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
                {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)})
              yNext
              (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
                n S (J + 1) e₂.symm (e₀κ.symm.trans eNext) c)) := by
  rcases
    exists_successorSourceChartMap_entrywise_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero
      n hS hcont hnext residual Cprime eNext hpivot with
    ⟨yNext, hentry⟩
  exact
    ⟨yNext,
      residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
        n hS hcont hnext residual Cprime C p yNext
        e₂ e₁ e₀κ eNext hD hF hentry⟩

set_option linter.style.longLine false in
/-- The successor selected-entry center-coordinate matrix on the continuing
Case 2 residual block.

This is finite selected-entry chart vocabulary.  It does not construct an
arbitrary retained-passive source/readback point. -/
noncomputable def case2SuccessorSelectedEntryMatrix
    {τ : Type*}
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ :=
  AoyagiResidualBlockCoordinateIndex.matrix
    (fun c : AoyagiResidualBlockCoordinateIndex
        (Case2ResidualRowIndex n S (J + 1)) τ ↦
      SelectedEntrySignedBox.CenterCoord.chartMap
        (⟨(J + 2, J + 2),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
            n hS hnext⟩ :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)})
        yNext
        (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
          n S (J + 1) (Equiv.refl _) eNext c))

set_option linter.style.longLine false in
/-- A nonzero successor selected pivot coordinate makes the successor
selected-entry matrix nonzero. -/
theorem case2SuccessorSelectedEntryMatrix_ne_zero_of_yNext_pivot_ne_zero
    {τ : Type*}
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hyNext :
      yNext (⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0) :
    case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext ≠ 0 := by
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
  intro hzero
  have hentry :
      case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext
          (residualCoordEquiv.symm pivotNext).1
          (residualCoordEquiv.symm pivotNext).2 =
        yNext pivotNext := by
    simp [case2SuccessorSelectedEntryMatrix, pivotNext, residualCoordEquiv,
      AoyagiResidualBlockCoordinateIndex.matrix]
  have hzero_entry :
      case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext
          (residualCoordEquiv.symm pivotNext).1
          (residualCoordEquiv.symm pivotNext).2 = 0 := by
    simpa using
      congrFun
        (congrFun hzero (residualCoordEquiv.symm pivotNext).1)
        (residualCoordEquiv.symm pivotNext).2
  exact hyNext (by
    simpa [pivotNext] using hentry.symm.trans hzero_entry)

set_option linter.style.longLine false in
/-- Construct displayed Case 2 finite data whose post-pivot free two-edge
product is the successor selected-entry matrix.

The residual block and `Cprime` are constructed: the residual realizes the
successor selected-entry matrix with its right endpoint reindexed, and the
following factor is the matching reindexed identity.  This removes the
displayed-product nonzeroness field only for constructed finite data; it does
not prove factor alignment or nonzeroness for an arbitrary retained-passive
source/readback point. -/
theorem exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
    {τ : Type*}
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hyNext :
      yNext (⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0) :
    ∃ residual : ℕ × ℕ → ℝ,
    ∃ Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ,
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime =
        case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext ∧
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime ≠ 0 := by
  let target :=
    case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext
  rcases
    exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_matrix_of_colEquiv
      n hS hcont target eNext with
    ⟨residual, Cprime, hprod⟩
  have htarget_ne : target ≠ 0 :=
    case2SuccessorSelectedEntryMatrix_ne_zero_of_yNext_pivot_ne_zero
      n hS hnext yNext eNext hyNext
  exact ⟨residual, Cprime, hprod, by
    rw [hprod]
    exact htarget_ne⟩

set_option linter.style.longLine false in
/-- Constructed concrete two-edge residual-factor family form of
`exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero`.

This packages the same constructed residual and free `Cprime` as the concrete
Case 2 two-edge factor family.  It removes generic factor-identity hypotheses
only for this constructed finite family, not for an arbitrary retained-passive
source/readback suffix. -/
theorem exists_residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hyNext :
      yNext (⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0) :
    ∃ residual : ℕ × ℕ → ℝ,
    ∃ Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ,
      ChartLocalSuffixState.residualFactorProduct
          (case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual Cprime)
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext ∧
      ChartLocalSuffixState.residualFactorProduct
          (case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual Cprime)
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) ≠ 0 := by
  rcases
    exists_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
      n hS hcont hnext yNext eNext hyNext with
    ⟨residual, Cprime, hprod, hprod_ne⟩
  have hrfp :
      ChartLocalSuffixState.residualFactorProduct
          (case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual Cprime)
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime :=
    residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_freeTwoEdgeFactorProduct
      n hS hcont residual Cprime
  refine ⟨residual, Cprime, ?_, ?_⟩
  · rw [hrfp, hprod]
  · intro hzero
    exact hprod_ne (by
      rw [← hrfp]
      exact hzero)

end Aoyagi
end DLN
end DLNFibre
