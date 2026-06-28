import DLNFibre.DLN.Aoyagi.Case2ResidualSelectedEntryChartBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology

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
/-- For the synthetic Case 2 retained-passive datum, the Schur residual block
of the transformed source edge at edge `1` is the displayed post-pivot residual
block. -/
theorem schurResidualBlock_sourceReadbackTransformedEdge_case2PostPivotRetainedPassiveData_edgeMatrix_one_eq_residualBlock
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ) :
    schurResidualBlock
        (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadbackTransformedEdge
            (K := ℝ) (ρ := ρ)
            (case2PostPivotRetainedPassiveData
              (ρ := ρ) n hS hcont residual Cprime).edgeMatrix
            (1 : Fin 2)) =
      case2DisplayedPostPivotResidualBlock n hS hcont residual := by
  have hC :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.schurResidualBlock_sourceReadbackTransformedEdge_edgeMatrix_eq_C
        (K := ℝ) (ρ := ρ)
        (data := case2PostPivotRetainedPassiveData
          (ρ := ρ) n hS hcont residual Cprime)
        (case2PostPivotRetainedPassiveData_detChart
          (ρ := ρ) n hS hcont residual Cprime)
        (1 : Fin 2)
  simpa [case2PostPivotRetainedPassiveData, case2PostPivotFreeTwoEdgeFactorFamily,
    case2PostPivotTwoEdgeDomain] using hC

set_option linter.style.longLine false in
/-- For the synthetic Case 2 retained-passive datum, the Schur residual block
of the transformed source edge at edge `0` is the displayed free following
factor. -/
theorem schurResidualBlock_sourceReadbackTransformedEdge_case2PostPivotRetainedPassiveData_edgeMatrix_zero_eq_freeFollowingFactor
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ) :
    schurResidualBlock
        (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadbackTransformedEdge
            (K := ℝ) (ρ := ρ)
            (case2PostPivotRetainedPassiveData
              (ρ := ρ) n hS hcont residual Cprime).edgeMatrix
            (0 : Fin 2)) =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime := by
  have hC :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.schurResidualBlock_sourceReadbackTransformedEdge_edgeMatrix_eq_C
        (K := ℝ) (ρ := ρ)
        (data := case2PostPivotRetainedPassiveData
          (ρ := ρ) n hS hcont residual Cprime)
        (case2PostPivotRetainedPassiveData_detChart
          (ρ := ρ) n hS hcont residual Cprime)
        (0 : Fin 2)
  simpa [case2PostPivotRetainedPassiveData, case2PostPivotFreeTwoEdgeFactorFamily,
    case2PostPivotTwoEdgeDomain] using hC

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
/-- A two-edge retained-passive coordinate datum satisfies the selected-entry
residual-factor matrix identity once its two `C` factors are Aoyagi's displayed
Case 2 post-pivot residual block and following factor, and the displayed
two-edge product is nonzero at the chosen selected pivot.

This replaces the full entrywise selected-entry readout by the finite
fixed-pivot inverse.  The nonzero-pivot hypothesis remains supplied; the theorem
does not prove source production or explain why this pivot should be nonzero. -/
theorem exists_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_pivot_ne_zero
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
    (hpivot :
      let productCoordEquiv :
          AoyagiResidualBlockCoordinateIndex
              (Case2ResidualRowIndex n S (J + 1)) τ ≃ center :=
        (Equiv.prodCongr e₂ e₀).trans residualCoordEquiv
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
        (productCoordEquiv.symm pivot).1 (productCoordEquiv.symm pivot).2 ≠ 0) :
    ∃ y : center → ℝ,
      ChartLocalSuffixState.residualFactorProduct data.C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c)) := by
  let D : Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ :=
    case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
  let productCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (Case2ResidualRowIndex n S (J + 1)) τ ≃ center :=
    (Equiv.prodCongr e₂ e₀).trans residualCoordEquiv
  have hpivot_D :
      D (productCoordEquiv.symm pivot).1 (productCoordEquiv.symm pivot).2 ≠ 0 := by
    simpa [D, productCoordEquiv] using hpivot
  rcases
    SelectedEntrySignedBox.CenterCoord.exists_matrix_eq_chartMap_of_pivot_ne_zero
      pivot D productCoordEquiv hpivot_D with
    ⟨y, hDchart⟩
  have hentry :
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv (e₂ i, e₀ t)) := by
    intro i t
    have hmatrix := congrFun (congrFun hDchart i) t
    simpa [D, productCoordEquiv, AoyagiResidualBlockCoordinateIndex.matrix] using hmatrix
  refine ⟨y, ?_⟩
  exact
    residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
      (ρ := ρ) (τ := τ) (ι := ι) (κ := κ) (center := center)
      pivot n hS hcont residual Cprime data y residualCoordEquiv e₂ e₁ e₀ hD hF hentry

set_option linter.style.longLine false in
/-- A two-edge retained-passive coordinate datum satisfies the selected-entry
residual-factor matrix identity for some selected pivot once its two `C` factors
are Aoyagi's displayed Case 2 post-pivot residual block and following factor,
and the displayed two-edge product matrix is nonzero.

This is the all-pivot finite selected-entry variant.  It still assumes
nonzeroness of the displayed product and does not prove source production. -/
theorem exists_pivot_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero
    {ρ τ ι : Type*} [DecidableEq ι]
    {κ : Fin 3 → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    {center : Finset ι}
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (data :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
        (K := ℝ) (ρ := ρ) κ)
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
    (hprod :
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime ≠ 0) :
    ∃ pivot : center, ∃ y : center → ℝ,
      ChartLocalSuffixState.residualFactorProduct data.C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c)) := by
  let D : Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ :=
    case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
  let productCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (Case2ResidualRowIndex n S (J + 1)) τ ≃ center :=
    (Equiv.prodCongr e₂ e₀).trans residualCoordEquiv
  have hD_nonzero : D ≠ 0 := by
    simpa [D] using hprod
  rcases
    SelectedEntrySignedBox.CenterCoord.exists_pivot_matrix_eq_chartMap_of_ne_zero
      D productCoordEquiv hD_nonzero with
    ⟨pivot, y, hDchart⟩
  have hentry :
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv (e₂ i, e₀ t)) := by
    intro i t
    have hmatrix := congrFun (congrFun hDchart i) t
    simpa [D, productCoordEquiv, AoyagiResidualBlockCoordinateIndex.matrix] using hmatrix
  refine ⟨pivot, y, ?_⟩
  exact
    residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
      (ρ := ρ) (τ := τ) (ι := ι) (κ := κ) (center := center)
      pivot n hS hcont residual Cprime data y residualCoordEquiv e₂ e₁ e₀ hD hF hentry

set_option linter.style.longLine false in
/-- The two-edge `ofTopologyTuple` specialization of the retained-passive
Case 2 selected-entry residual-factor product bridge.

This is only a whole-suffix statement when the retained-passive suffix has
two edges (`M = 1`).  It keeps the displayed factor identities and entrywise
selected-entry readout explicit. -/
theorem residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
    {ρ τ ι : Type*} [DecidableEq ι]
    {κ : Fin 3 → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    {center : Finset ι} (pivot : center)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (z :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.TopologyTuple
        (M := 1) ρ κ ℝ)
    (y : center → ℝ)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ≃ center)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ (Fin.last 2))
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ (1 : Fin 3))
    (e₀ : τ ≃ κ 0)
    (hD :
      (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) ℝ from
        by simpa using
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
            (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z).C (1 : Fin 2)).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ (1 : Fin 3)) (κ 0) ℝ from
        by simpa using
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
            (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z).C (0 : Fin 2)).submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
    (hentry :
      ∀ i t,
        case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime i t =
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv (e₂ i, e₀ t))) :
    ChartLocalSuffixState.residualFactorProduct
        (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
          (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z).C
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
          SelectedEntrySignedBox.CenterCoord.chartMap pivot y
            (residualCoordEquiv c)) := by
  exact
    residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise
      (ρ := ρ) (τ := τ) (ι := ι) (κ := κ) (center := center)
      pivot n hS hcont residual Cprime
      (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
        (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z)
      y residualCoordEquiv e₂ e₁ e₀ hD hF hentry

set_option linter.style.longLine false in
/-- The two-edge `ofTopologyTuple` specialization with the entrywise
selected-entry readout replaced by a supplied nonzero selected pivot of the
displayed post-pivot product. -/
theorem exists_residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_pivot_ne_zero
    {ρ τ ι : Type*} [DecidableEq ι]
    {κ : Fin 3 → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    {center : Finset ι} (pivot : center)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (z :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.TopologyTuple
        (M := 1) ρ κ ℝ)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ≃ center)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ (Fin.last 2))
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ (1 : Fin 3))
    (e₀ : τ ≃ κ 0)
    (hD :
      (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) ℝ from
        by simpa using
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
            (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z).C (1 : Fin 2)).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ (1 : Fin 3)) (κ 0) ℝ from
        by simpa using
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
            (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z).C (0 : Fin 2)).submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
    (hpivot :
      let productCoordEquiv :
          AoyagiResidualBlockCoordinateIndex
              (Case2ResidualRowIndex n S (J + 1)) τ ≃ center :=
        (Equiv.prodCongr e₂ e₀).trans residualCoordEquiv
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
        (productCoordEquiv.symm pivot).1 (productCoordEquiv.symm pivot).2 ≠ 0) :
    ∃ y : center → ℝ,
      ChartLocalSuffixState.residualFactorProduct
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
            (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c)) := by
  exact
    exists_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_pivot_ne_zero
      (ρ := ρ) (τ := τ) (ι := ι) (κ := κ) (center := center)
      pivot n hS hcont residual Cprime
      (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
        (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z)
      residualCoordEquiv e₂ e₁ e₀ hD hF hpivot

set_option linter.style.longLine false in
/-- The two-edge `ofTopologyTuple` specialization with the selected pivot chosen
from a nonzero displayed post-pivot product matrix.

This is an all-pivot finite selected-entry adapter.  It still assumes the
displayed product matrix is nonzero and does not prove source production or
factor alignment for an actual fixed-base source chart. -/
theorem exists_pivot_residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero
    {ρ τ ι : Type*} [DecidableEq ι]
    {κ : Fin 3 → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    {center : Finset ι}
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (z :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.TopologyTuple
        (M := 1) ρ κ ℝ)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ≃ center)
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ (Fin.last 2))
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ (1 : Fin 3))
    (e₀ : τ ≃ κ 0)
    (hD :
      (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) ℝ from
        by simpa using
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
            (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z).C (1 : Fin 2)).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ (1 : Fin 3)) (κ 0) ℝ from
        by simpa using
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
            (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z).C (0 : Fin 2)).submatrix e₁ e₀ =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
    (hprod :
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime ≠ 0) :
    ∃ pivot : center, ∃ y : center → ℝ,
      ChartLocalSuffixState.residualFactorProduct
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
            (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex (κ (Fin.last 2)) (κ 0) ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c)) := by
  exact
    exists_pivot_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero
      (ρ := ρ) (τ := τ) (ι := ι) (κ := κ) (center := center)
      n hS hcont residual Cprime
      (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple
        (M := 1) (K := ℝ) (ρ := ρ) (κ' := κ) z)
      residualCoordEquiv e₂ e₁ e₀ hD hF hprod

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
/-- If the displayed post-pivot product has nonzero successor pivot, an
adjacent two-edge window in a longer retained-passive coordinate datum admits
successor selected-entry coordinates whose center-coordinate matrix is that
adjacent residual-factor product.

The adjacent window, endpoint equivalences, and factor identities are supplied.
This theorem does not identify a full retained-passive suffix or fixed-base
source chart with this adjacent window. -/
theorem exists_residualFactorProduct_retainedPassiveCoordinateData_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2PostPivot_pivot_ne_zero
    {ρ τ : Type*} {N : ℕ}
    {κ : Fin (N + 3) → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → ℝ)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ ℝ)
    (data :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
        (K := ℝ) (ρ := ρ) κ)
    (p : Fin (N + 1))
    (e₂ : Case2ResidualRowIndex n S (J + 1) ≃ κ p.succ.succ)
    (e₁ : Case2ResidualColIndex n S (J + 1) ≃ κ p.succ.castSucc)
    (e₀κ : τ ≃ κ p.castSucc.castSucc)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hD :
      (show Matrix (κ p.succ.succ) (κ p.succ.castSucc) ℝ from
        by simpa using data.C p.succ).submatrix e₂ e₁ =
      case2DisplayedPostPivotResidualBlock n hS hcont residual)
    (hF :
      (show Matrix (κ p.succ.castSucc) (κ p.castSucc.castSucc) ℝ from
        by simpa using data.C p.castSucc).submatrix e₁ e₀κ =
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
      ChartLocalSuffixState.residualFactorProduct data.C
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
  exact
    exists_residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero
      n hS hcont hnext residual Cprime data.C p e₂ e₁ e₀κ eNext hD hF hpivot

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

set_option linter.style.longLine false in
/-- Constructed source-recursive Case 2 source data whose actual
`sourceReadback` residual-factor product is the successor selected-entry
matrix.

This theorem passes the finite constructed Case 2 data through the
retained-passive source map/readback pair: the source family is the `edgeMatrix`
of the synthetic two-edge retained-passive datum, and the determinant-chart
readback-after-source inverse theorem identifies its `sourceReadback` with that datum.  It is
constructed source data only; it does not prove arbitrary retained-passive
coverage, source-prior transport, normal crossings, pole order, or RLCT. -/
theorem exists_sourceRecursive_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
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
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
          (K := ℝ) (ρ := ρ)
          (case2PostPivotRetainedPassiveData
            (ρ := ρ) n hS hcont residual Cprime).edgeMatrix ∧
      ChartLocalSuffixState.residualFactorProduct
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
            (K := ℝ) (ρ := ρ)
            (case2PostPivotRetainedPassiveData
              (ρ := ρ) n hS hcont residual Cprime).edgeMatrix).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext ∧
      ChartLocalSuffixState.residualFactorProduct
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
            (K := ℝ) (ρ := ρ)
            (case2PostPivotRetainedPassiveData
              (ρ := ρ) n hS hcont residual Cprime).edgeMatrix).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) ≠ 0 := by
  rcases
    exists_residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
      n hS hcont hnext yNext eNext hyNext with
    ⟨residual, Cprime, hprod, hprod_ne⟩
  let data :=
    case2PostPivotRetainedPassiveData
      (ρ := ρ) n hS hcont residual Cprime
  have hdet : data.detChart :=
    case2PostPivotRetainedPassiveData_detChart
      (ρ := ρ) n hS hcont residual Cprime
  have hsource :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
          (K := ℝ) (ρ := ρ) data.edgeMatrix :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart_edgeMatrix_of_detChart
      (K := ℝ) (ρ := ρ) data hdet
  have hread :
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
          (K := ℝ) (ρ := ρ) data.edgeMatrix = data :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_edgeMatrix_eq
      (K := ℝ) (ρ := ρ) (data := data) hdet
  have hC :
      (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
          (K := ℝ) (ρ := ρ) data.edgeMatrix).C =
        data.C := by
    exact congrArg
      (fun data' :
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) ↦ data'.C)
      hread
  have hsourceProduct :
      ChartLocalSuffixState.residualFactorProduct
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
            (K := ℝ) (ρ := ρ) data.edgeMatrix).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        ChartLocalSuffixState.residualFactorProduct
          (case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual Cprime)
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) := by
    rw [hC]
    rfl
  refine ⟨residual, Cprime, ?_, ?_, ?_⟩
  · simpa [data] using hsource
  · exact hsourceProduct.trans hprod
  · intro hzero
    exact hprod_ne (by
      rw [← hsourceProduct]
      exact hzero)

set_option linter.style.longLine false in
/-- Standalone source-edge-family form of
`exists_sourceRecursive_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero`.

The produced source family is the retained-passive source map of the synthetic
Case 2 datum.  This is constructed source production in the two-edge Case 2
window, not arbitrary retained-passive coverage. -/
theorem exists_sourceRecursiveEdgeFamily_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
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
    ∃ E : ∀ p : Fin 2,
      Matrix
        (ρ ⊕ case2PostPivotTwoEdgeDomain n S J τ p.succ)
        (ρ ⊕ case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ,
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
          (K := ℝ) (ρ := ρ) E ∧
      ChartLocalSuffixState.residualFactorProduct
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
            (K := ℝ) (ρ := ρ) E).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext ∧
      ChartLocalSuffixState.residualFactorProduct
          (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
            (K := ℝ) (ρ := ρ) E).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) ≠ 0 := by
  rcases
    exists_sourceRecursive_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
      (ρ := ρ) n hS hcont hnext yNext eNext hyNext with
    ⟨residual, Cprime, hsource, hprod, hprod_ne⟩
  exact
    ⟨(case2PostPivotRetainedPassiveData
        (ρ := ρ) n hS hcont residual Cprime).edgeMatrix,
      hsource, hprod, hprod_ne⟩

end Aoyagi
end DLN
end DLNFibre
