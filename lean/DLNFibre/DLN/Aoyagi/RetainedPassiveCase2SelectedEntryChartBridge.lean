import DLNFibre.DLN.Aoyagi.Case2ResidualSelectedEntryChartBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates

/-!
# Retained-passive Case 2 selected-entry residual bridge

This file specializes the finite Case 2 residual-factor product bridge to a
two-edge retained-passive coordinate datum.  It is finite matrix algebra only.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The synthetic two-edge retained-passive datum whose active `C` factors are
Aoyagi's displayed Case 2 post-pivot residual block and following factor.

All passive retained coordinates are set to zero, while `Ctop` and the single
passive `A1` block are identity matrices.  This is a finite bookkeeping object;
it does not construct a source chart or identify a longer retained-passive
suffix with the displayed two-edge chain. -/
noncomputable def case2PostPivotRetainedPassiveData
    {ρ : Type*} {τ : Type} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ) :
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
      (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) where
  A1passive := fun _ ↦ 1
  F2 := fun _ ↦ 0
  A3passive := fun _ ↦ 0
  C := case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual Cprime
  Ctop := 1
  F3 := 0

/-- The synthetic two-edge Case 2 retained-passive datum lies in the finite
retained-passive determinant chart. -/
theorem case2PostPivotRetainedPassiveData_detChart
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ) :
    (case2PostPivotRetainedPassiveData
      (ρ := ρ) n hS hcont residual Cprime).detChart := by
  constructor
  · simp [case2PostPivotRetainedPassiveData]
  · intro p
    simp [case2PostPivotRetainedPassiveData]

set_option linter.style.longLine false in
/-- A two-edge retained-passive coordinate datum satisfies the selected-entry
residual-factor matrix identity once its two `C` factors are Aoyagi's displayed
Case 2 post-pivot residual block and following factor.

This is finite Case 2 algebra only.  The order is `data.C 1` for the
post-pivot residual block followed by `data.C 0` for the free following factor,
both on the shifted `(S, J + 1)` residual domains.  The entrywise selected-center
readout remains an explicit hypothesis. -/
theorem residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
    {ρ τ ι : Type*} [DecidableEq ι]
    {κ : Fin 3 → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    {center : Finset ι} (pivot : center)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (data :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
        (K := ℝ) (ρ := ρ) κ)
    (y : center → ℝ)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ≃ center)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ (Fin.last 2))
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ (1 : Fin 3))
    (e₀ : τ ≃ κ 0)
    (hD :
      (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) ℝ from
        by simpa using data.C (1 : Fin 2)).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ (1 : Fin 3)) (κ 0) ℝ from
        by simpa using data.C (0 : Fin 2)).submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
    (hentry :
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv (e₂ i, e₀ t))) :
    ChartLocalSuffixState.residualFactorProduct data.C
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv c)) := by
  exact
    residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
      n hS hcont residual Cprime data.C
      (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)
      residualCoordEquiv e₂ e₁ e₀ hD hF hentry

set_option linter.style.longLine false in
/-- Source-shaped Case 2 specialization for a two-edge retained-passive
coordinate datum.

The conclusion is the successor selected-entry center-coordinate matrix on the
post-pivot `(S, J + 1)` residual block.  The factor order is still `data.C 1`
then `data.C 0`; the entrywise displayed-source readout is the mathematical
hypothesis that identifies the product with successor chart coordinates. -/
theorem residualFactorProduct_retainedPassiveCoordinateData_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2PostPivot_entrywise
    {ρ τ : Type*}
    {κ : Fin 3 → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (data :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
        (K := ℝ) (ρ := ρ) κ)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ (Fin.last 2))
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ (1 : Fin 3))
    (e₀κ : τ ≃ κ 0)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hD :
      (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) ℝ from
        by simpa using data.C (1 : Fin 2)).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ (1 : Fin 3)) (κ 0) ℝ from
        by simpa using data.C (0 : Fin 2)).submatrix e₁ e₀κ =
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
    ChartLocalSuffixState.residualFactorProduct data.C
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
          SelectedEntrySignedBox.CenterCoord.chartMap
            (⟨(J + 2, J + 2),
              case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
              {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)})
            yNext
            (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) e₂.symm (e₀κ.symm.trans eNext) c)) := by
  exact
    residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
      n hS hcont hnext residual Cprime data.C yNext e₂ e₁ e₀κ eNext hD hF hentry

set_option linter.style.longLine false in
/-- The synthetic two-edge retained-passive Case 2 datum satisfies the
successor selected-entry residual-factor matrix identity.

This removes the generic retained-passive factor-identification hypotheses by
choosing the active factors to be exactly Aoyagi's displayed post-pivot two-edge
family.  The entrywise successor-source readout remains an explicit hypothesis,
and this theorem is still finite matrix algebra only. -/
theorem case2PostPivotRetainedPassiveData_hdataFactor_of_entrywise
    {ρ : Type*} {τ : Type} [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
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
        (case2PostPivotRetainedPassiveData
          (ρ := ρ) n hS hcont residual Cprime).C
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
  simpa [case2PostPivotRetainedPassiveData] using
    residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
      (τ := τ) n hS hcont hnext residual Cprime yNext eNext hentry

set_option linter.style.longLine false in
/-- Content-named alias for
`case2PostPivotRetainedPassiveData_hdataFactor_of_entrywise`. -/
theorem case2PostPivotRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
    {ρ : Type*} {τ : Type} [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
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
        (case2PostPivotRetainedPassiveData
          (ρ := ρ) n hS hcont residual Cprime).C
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
              n S (J + 1) (Equiv.refl _) eNext c)) :=
  case2PostPivotRetainedPassiveData_hdataFactor_of_entrywise
    (ρ := ρ) n hS hcont hnext residual Cprime yNext eNext hentry

set_option linter.style.longLine false in
/-- If the displayed post-pivot product has nonzero successor pivot, the
synthetic retained-passive Case 2 datum admits successor selected-entry
coordinates whose center-coordinate matrix is its residual-factor product.

The fixed-pivot nonzero hypothesis is still supplied.  This theorem only
replaces the full entrywise source-chart readout by the finite selected-entry
inverse at that pivot. -/
theorem exists_case2PostPivotRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_pivot_ne_zero
    {ρ : Type*} {τ : Type} [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
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
      ChartLocalSuffixState.residualFactorProduct
          (case2PostPivotRetainedPassiveData
            (ρ := ρ) n hS hcont residual Cprime).C
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
  rcases
    exists_successorSourceChartMap_entrywise_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero
      n hS hcont hnext residual Cprime eNext hpivot with
    ⟨yNext, hentry⟩
  exact
    ⟨yNext,
      case2PostPivotRetainedPassiveData_hdataFactor_of_entrywise
        (ρ := ρ) n hS hcont hnext residual Cprime yNext eNext hentry⟩

end Aoyagi
end DLN
end DLNFibre
