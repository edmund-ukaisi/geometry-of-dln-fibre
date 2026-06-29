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

/-- Submatrixing first by inverse endpoint equivalences and then by the forward
equivalences recovers the original matrix. -/
theorem matrix_submatrix_equiv_symm_submatrix_equiv
    {ι κ ι' κ' R : Type*} (A : Matrix ι κ R)
    (eι : ι ≃ ι') (eκ : κ ≃ κ') :
    (A.submatrix eι.symm eκ.symm).submatrix eι eκ = A := by
  simp only [Matrix.submatrix_submatrix, Matrix.submatrix_id_id,
    Equiv.symm_comp_self]

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
/-- Explicit retained-passive datum attached to successor selected-entry
coordinates in the continuing Case 2 branch. -/
noncomputable def case2PostPivotSelectedEntryRetainedPassiveData
    {ρ : Type*} {τ : Type} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
      (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) :=
  case2PostPivotRetainedPassiveData (ρ := ρ) n hS hcont
    (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
    (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext)

set_option linter.style.longLine false in
/-- Passive-parameter variant of the explicit selected-entry retained-passive
datum.

The selected-entry coordinates still control only the two residual `C` factors.
The remaining retained-passive coordinates are supplied as independent
parameters.  This is the first finite coordinate object large enough to keep
the passive variables that the reduced selected-entry section fixes. -/
noncomputable def case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
    {ρ : Type*} {τ : Type} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
      (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) where
  A1passive := A1passive
  F2 := F2
  A3passive := A3passive
  C := case2PostPivotFreeTwoEdgeFactorFamily n hS hcont
    (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
    (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext)
  Ctop := Ctop
  F3 := F3

set_option linter.style.longLine false in
/-- The explicit selected-entry retained-passive datum lies in the finite
retained-passive determinant chart for every coordinate vector `yNext`. -/
theorem case2PostPivotSelectedEntryRetainedPassiveData_detChart
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    (case2PostPivotSelectedEntryRetainedPassiveData
      (ρ := ρ) n hS hcont hnext yNext eNext).detChart := by
  simpa [case2PostPivotSelectedEntryRetainedPassiveData] using
    case2PostPivotRetainedPassiveData_detChart
      (ρ := ρ) n hS hcont
      (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
      (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext)

set_option linter.style.longLine false in
/-- The passive-parameter selected-entry retained-passive datum lies in the
determinant chart under the supplied active top-block and passive `A1` unit
hypotheses. -/
theorem case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_detChart
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hCtop : IsUnit Ctop.det)
    (hA1passive : ∀ p : Fin 1, IsUnit (A1passive p).det) :
    (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
      (ρ := ρ) n hS hcont hnext A1passive F2 A3passive Ctop F3
      yNext eNext).detChart := by
  constructor
  · simpa [case2PostPivotSelectedEntryRetainedPassiveDataWithPassive] using hCtop
  · intro p
    simpa [case2PostPivotSelectedEntryRetainedPassiveDataWithPassive] using
      hA1passive p

set_option linter.style.longLine false in
/-- Endpoint transport preserves the determinant-chart proof for the explicit
selected-entry Case 2 retained-passive datum. -/
theorem case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    ((case2PostPivotSelectedEntryRetainedPassiveData
      (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e).detChart := by
  simpa using
    case2PostPivotSelectedEntryRetainedPassiveData_detChart
      (ρ := ρ) n hS hcont hnext yNext eNext

set_option linter.style.longLine false in
/-- Endpoint transport preserves the determinant-chart proof for the
passive-parameter selected-entry Case 2 retained-passive datum. -/
theorem case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (hCtop : IsUnit Ctop.det)
    (hA1passive : ∀ p : Fin 1, IsUnit (A1passive p).det) :
    ((case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
      (ρ := ρ) n hS hcont hnext A1passive F2 A3passive Ctop F3
      yNext eNext).endpointTransport e).detChart := by
  simpa using
    case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_detChart
      (ρ := ρ) n hS hcont hnext A1passive F2 A3passive Ctop F3
      yNext eNext hCtop hA1passive

set_option linter.style.longLine false in
/-- The explicit selected-entry retained-passive datum is continuous as a
function of the successor selected-entry coordinates. -/
theorem continuous_case2PostPivotSelectedEntryRetainedPassiveData
    {ρ : Type*} {τ : Type} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    Continuous
      (fun yNext :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ ↦
        case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext yNext eNext) := by
  have hC :
      Continuous
        (fun yNext :
            {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ ↦
          case2PostPivotFreeTwoEdgeFactorFamily n hS hcont
            (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
            (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext)) := by
    refine continuous_pi ?_
    intro p
    fin_cases p
    · simpa [case2PostPivotFreeTwoEdgeFactorFamily,
        case2SuccessorSelectedEntrySourceCprime,
        case2DisplayedPostPivotFreeCprimeOfMatrix, case2PostPivotTwoEdgeDomain] using
        (continuous_const :
          Continuous
            (fun _yNext :
                {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ ↦
              case2DisplayedPostPivotFreeFollowingFactor n hS hcont
                (case2DisplayedPostPivotFreeCprimeOfMatrix n hS hcont
                  (case2SuccessorSelectedEntryMatrix n hS hnext
                    (fun _ ↦ 0) eNext) eNext)))
    · have hM :
          Continuous
            (fun yNext :
                {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ ↦
              (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).submatrix
                id eNext.symm) :=
        (continuous_case2SuccessorSelectedEntryMatrix n hS hnext eNext).matrix_submatrix
          id eNext.symm
      have htarget :
          (fun yNext :
              {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ ↦
            case2PostPivotFreeTwoEdgeFactorFamily n hS hcont
              (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
              (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext) 1) =
          (fun yNext ↦
            (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).submatrix
              id eNext.symm) := by
        funext yNext
        ext i j
        change
          case2DisplayedPostPivotResidualBlock n hS hcont
              (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext) i j =
            case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext i (eNext.symm j)
        simp [case2SuccessorSelectedEntrySourceResidual,
          case2DisplayedPostPivotSourceResidualOfMatrix,
          case2DisplayedPostPivotResidualBlock_sourceResidualBlockExtension]
      change Continuous
        (fun yNext :
            {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ ↦
          case2PostPivotFreeTwoEdgeFactorFamily n hS hcont
            (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
            (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext) 1)
      rw [htarget]
      exact hM
  let kappa : Fin 3 → Type := case2PostPivotTwoEdgeDomain n S J τ
  have htuple :
      Continuous
        (fun yNext :
            {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ ↦
          ((fun _ : Fin 1 ↦ (1 : Matrix ρ ρ ℝ)),
            ((fun p : Fin 2 ↦ (0 : Matrix ρ (kappa (p.castSucc)) ℝ)),
              ((fun p : Fin 1 ↦ (0 : Matrix (kappa (p.castSucc.succ)) ρ ℝ)),
                (case2PostPivotFreeTwoEdgeFactorFamily n hS hcont
                  (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
                  (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext),
                  ((1 : Matrix ρ ρ ℝ),
                    (0 : Matrix (kappa (Fin.last 2)) ρ ℝ))))))) := by
    exact
      continuous_const.prodMk
        (continuous_const.prodMk
          (continuous_const.prodMk
            (hC.prodMk (continuous_const.prodMk continuous_const))))
  simpa [ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple,
    case2PostPivotSelectedEntryRetainedPassiveData, case2PostPivotRetainedPassiveData, kappa] using
    (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_ofTopologyTuple
      (K := ℝ) (ρ := ρ) (κ' := kappa)).comp htuple

set_option linter.style.longLine false in
/-- Passive-parameter selected-entry retained-passive data are continuous when
the passive fields are continuous in the passive parameter and the selected
entry coordinates vary in the second component.

This is coordinatewise/product-topology regularity only.  It does not prove
determinant membership, source-image coverage, a measure pushforward, a
Jacobian formula, normal crossings, pole order, or RLCT. -/
theorem continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
    {η ρ : Type*} [TopologicalSpace η] {τ : Type} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (A1passive : η → Fin 1 → Matrix ρ ρ ℝ)
    (F2 : η → ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : η → Matrix ρ ρ ℝ)
    (F3 : η → Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (hA1passive_cont : Continuous A1passive)
    (hF2_cont : Continuous F2)
    (hA3passive_cont : Continuous A3passive)
    (hCtop_cont : Continuous Ctop)
    (hF3_cont : Continuous F3) :
    Continuous
      (fun z :
          η ×
            ({p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ) ↦
        case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := ρ) n hS hcont hnext
          (A1passive z.1) (F2 z.1) (A3passive z.1) (Ctop z.1)
          (F3 z.1) z.2 eNext) := by
  let kappa : Fin 3 → Type := case2PostPivotTwoEdgeDomain n S J τ
  let selectedData :
      ({p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ) →
        ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) kappa :=
    fun yNext ↦
      case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext
  have hselected : Continuous selectedData := by
    simpa [selectedData, kappa] using
      continuous_case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext eNext
  have hC :
      Continuous
        (fun z :
            η ×
              ({p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ) ↦
          (selectedData z.2).C) := by
    refine continuous_pi ?_
    intro p
    exact (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_C
      (K := ℝ) (ρ := ρ) (κ' := kappa) p).comp (hselected.comp continuous_snd)
  have htuple :
      Continuous
        (fun z :
            η ×
              ({p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ) ↦
          (A1passive z.1,
            (F2 z.1,
              (A3passive z.1,
                ((selectedData z.2).C,
                  (Ctop z.1, F3 z.1)))))) := by
    exact
      (hA1passive_cont.comp continuous_fst).prodMk
        ((hF2_cont.comp continuous_fst).prodMk
          ((hA3passive_cont.comp continuous_fst).prodMk
            (hC.prodMk
              ((hCtop_cont.comp continuous_fst).prodMk
                (hF3_cont.comp continuous_fst)))))
  simpa [ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.ofTopologyTuple,
    case2PostPivotSelectedEntryRetainedPassiveDataWithPassive, selectedData, kappa] using
    (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_ofTopologyTuple
      (K := ℝ) (ρ := ρ) (κ' := kappa)).comp htuple

set_option linter.style.longLine false in
/-- The explicit selected-entry retained-passive datum is continuous as a map
into the retained-passive determinant-chart subtype. -/
theorem continuous_case2PostPivotSelectedEntryRetainedPassiveData_detChart_subtype
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    Continuous
      (fun yNext :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ ↦
        (⟨case2PostPivotSelectedEntryRetainedPassiveData
            (ρ := ρ) n hS hcont hnext yNext eNext,
          case2PostPivotSelectedEntryRetainedPassiveData_detChart
            (ρ := ρ) n hS hcont hnext yNext eNext⟩ :
          {data : ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
              (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) //
            data.detChart})) :=
  (continuous_case2PostPivotSelectedEntryRetainedPassiveData
    (ρ := ρ) n hS hcont hnext eNext).subtype_mk _

set_option linter.style.longLine false in
/-- Explicit source edge family attached to successor selected-entry
coordinates in the continuing Case 2 branch. -/
noncomputable def case2PostPivotSelectedEntrySourceEdgeFamily
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    ∀ p : Fin 2,
      Matrix
        (ρ ⊕ case2PostPivotTwoEdgeDomain n S J τ p.succ)
        (ρ ⊕ case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ :=
  (case2PostPivotSelectedEntryRetainedPassiveData
    (ρ := ρ) n hS hcont hnext yNext eNext).edgeMatrix

set_option linter.style.longLine false in
/-- The explicit selected-entry source edge family is continuous as a function
of the successor selected-entry coordinates. -/
theorem continuous_case2PostPivotSelectedEntrySourceEdgeFamily
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    Continuous
      (fun yNext :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ ↦
        case2PostPivotSelectedEntrySourceEdgeFamily
          (ρ := ρ) n hS hcont hnext yNext eNext) := by
  have hdata :=
    continuous_case2PostPivotSelectedEntryRetainedPassiveData_detChart_subtype
      (ρ := ρ) n hS hcont hnext eNext
  have hedge :
      Continuous
        (fun data :
            {data : ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
                (K := ℝ) (ρ := ρ) (case2PostPivotTwoEdgeDomain n S J τ) //
              data.detChart} ↦ data.1.edgeMatrix) :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_edgeMatrix_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := case2PostPivotTwoEdgeDomain n S J τ)
  simpa [case2PostPivotSelectedEntrySourceEdgeFamily] using hedge.comp hdata

set_option linter.style.longLine false in
/-- The explicit selected-entry source edge family is measurable as a function
of the successor selected-entry coordinates. -/
theorem measurable_case2PostPivotSelectedEntrySourceEdgeFamily
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    Measurable
      (fun yNext :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ ↦
        case2PostPivotSelectedEntrySourceEdgeFamily
          (ρ := ρ) n hS hcont hnext yNext eNext) :=
  (continuous_case2PostPivotSelectedEntrySourceEdgeFamily
    (ρ := ρ) n hS hcont hnext eNext).measurable

set_option linter.style.longLine false in
/-- The explicit selected-entry source edge family lies in the source-recursive
determinant chart. -/
theorem case2PostPivotSelectedEntrySourceEdgeFamily_sourceRecursiveDetChart
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart
        (K := ℝ) (ρ := ρ)
        (case2PostPivotSelectedEntrySourceEdgeFamily
          (ρ := ρ) n hS hcont hnext yNext eNext) := by
  let data :=
    case2PostPivotSelectedEntryRetainedPassiveData
      (ρ := ρ) n hS hcont hnext yNext eNext
  have hdet : data.detChart :=
    case2PostPivotSelectedEntryRetainedPassiveData_detChart
      (ρ := ρ) n hS hcont hnext yNext eNext
  simpa [case2PostPivotSelectedEntrySourceEdgeFamily, data] using
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart_edgeMatrix_of_detChart
      (K := ℝ) (ρ := ρ) data hdet

set_option linter.style.longLine false in
/-- The first edge of the explicit continuing Case 2 selected-entry source
family has rank `card rho + card tau`.

This is a finite edge-rank computation for the constructed source family.  It
does not assert membership in a fixed source-rank stratum, choose `rEdge`, or
prove source coverage. -/
theorem rank_case2PostPivotSelectedEntrySourceEdgeFamily_zero
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    (case2PostPivotSelectedEntrySourceEdgeFamily
        (ρ := ρ) n hS hcont hnext yNext eNext 0).rank =
      Fintype.card ρ + Fintype.card τ := by
  let data :=
    case2PostPivotSelectedEntryRetainedPassiveData
      (ρ := ρ) n hS hcont hnext yNext eNext
  have hdet : data.detChart :=
    case2PostPivotSelectedEntryRetainedPassiveData_detChart
      (ρ := ρ) n hS hcont hnext yNext eNext
  have hedge :
      (data.edgeMatrix (0 : Fin 2)).rank =
        Fintype.card ρ + (data.C (0 : Fin 2)).rank :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_edgeMatrix
      (K := ℝ) (ρ := ρ) data hdet (0 : Fin 2)
  have hC :
      (data.C (0 : Fin 2)).rank = Fintype.card τ := by
    simpa [data, case2PostPivotSelectedEntryRetainedPassiveData,
      case2PostPivotRetainedPassiveData, case2PostPivotFreeTwoEdgeFactorFamily,
      case2SuccessorSelectedEntrySourceCprime] using
      rank_case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfMatrix
        n hS hcont
        (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) eNext
  calc
    (case2PostPivotSelectedEntrySourceEdgeFamily
        (ρ := ρ) n hS hcont hnext yNext eNext 0).rank =
        (data.edgeMatrix (0 : Fin 2)).rank := by
      rfl
    _ = Fintype.card ρ + (data.C (0 : Fin 2)).rank := hedge
    _ = Fintype.card ρ + Fintype.card τ := by rw [hC]

set_option linter.style.longLine false in
/-- The second edge of the explicit continuing Case 2 selected-entry source
family has rank `card rho` plus the rank of the successor selected-entry
matrix.

This is a finite edge-rank computation for the constructed source family.  It
does not assert a numerical successor residual rank unless a separate exact
rank hypothesis for the successor matrix is supplied. -/
theorem rank_case2PostPivotSelectedEntrySourceEdgeFamily_one
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    (case2PostPivotSelectedEntrySourceEdgeFamily
        (ρ := ρ) n hS hcont hnext yNext eNext 1).rank =
      Fintype.card ρ +
        (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank := by
  let data :=
    case2PostPivotSelectedEntryRetainedPassiveData
      (ρ := ρ) n hS hcont hnext yNext eNext
  have hdet : data.detChart :=
    case2PostPivotSelectedEntryRetainedPassiveData_detChart
      (ρ := ρ) n hS hcont hnext yNext eNext
  have hedge :
      (data.edgeMatrix (1 : Fin 2)).rank =
        Fintype.card ρ + (data.C (1 : Fin 2)).rank :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.rank_edgeMatrix
      (K := ℝ) (ρ := ρ) data hdet (1 : Fin 2)
  have hC :
      (data.C (1 : Fin 2)).rank =
        (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank := by
    simpa [data, case2PostPivotSelectedEntryRetainedPassiveData,
      case2PostPivotRetainedPassiveData, case2PostPivotFreeTwoEdgeFactorFamily,
      case2SuccessorSelectedEntrySourceResidual] using
      rank_case2DisplayedPostPivotResidualBlock_sourceResidualOfMatrix
        n hS hcont
        (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) eNext
  calc
    (case2PostPivotSelectedEntrySourceEdgeFamily
        (ρ := ρ) n hS hcont hnext yNext eNext 1).rank =
        (data.edgeMatrix (1 : Fin 2)).rank := by
      rfl
    _ = Fintype.card ρ + (data.C (1 : Fin 2)).rank := hedge
    _ = Fintype.card ρ +
        (case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext).rank := by
      rw [hC]

set_option linter.style.longLine false in
/-- Readback of the explicit selected-entry source edge family recovers the
explicit selected-entry retained-passive datum. -/
theorem case2PostPivotSelectedEntrySourceReadback_eq_retainedPassiveData
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
        (K := ℝ) (ρ := ρ)
        (case2PostPivotSelectedEntrySourceEdgeFamily
          (ρ := ρ) n hS hcont hnext yNext eNext) =
      case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext := by
  let data :=
    case2PostPivotSelectedEntryRetainedPassiveData
      (ρ := ρ) n hS hcont hnext yNext eNext
  have hdet : data.detChart :=
    case2PostPivotSelectedEntryRetainedPassiveData_detChart
      (ρ := ρ) n hS hcont hnext yNext eNext
  simpa [case2PostPivotSelectedEntrySourceEdgeFamily, data] using
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_edgeMatrix_eq
      (K := ℝ) (ρ := ρ) (data := data) hdet

set_option linter.style.longLine false in
/-- The explicit selected-entry source edge family's actual readback has
residual-factor product equal to the successor selected-entry matrix.

This is a parametric source-chart statement: no witness is chosen by
`Classical.choose`, and no nonzero pivot hypothesis is needed for the equality. -/
theorem case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    ChartLocalSuffixState.residualFactorProduct
        (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
          (K := ℝ) (ρ := ρ)
          (case2PostPivotSelectedEntrySourceEdgeFamily
            (ρ := ρ) n hS hcont hnext yNext eNext)).C
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
      case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext := by
  have hread :=
    case2PostPivotSelectedEntrySourceReadback_eq_retainedPassiveData
      (ρ := ρ) n hS hcont hnext yNext eNext
  rw [hread]
  simpa [case2PostPivotSelectedEntryRetainedPassiveData] using
    residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_successorSelectedEntrySource_eq
      n hS hcont hnext yNext eNext

set_option linter.style.longLine false in
/-- The explicit selected-entry source edge family's actual readback has
residual-factor product equal to the selected-entry center-coordinate matrix.

This is the same finite equality as
`case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix`,
with the successor selected-entry matrix unfolded into the exact matrix shape
used by selected-entry local-measure handoffs. -/
theorem case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    ChartLocalSuffixState.residualFactorProduct
        (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
          (K := ℝ) (ρ := ρ)
          (case2PostPivotSelectedEntrySourceEdgeFamily
            (ρ := ρ) n hS hcont hnext yNext eNext)).C
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
  simpa [case2SuccessorSelectedEntryMatrix] using
    case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix
      (ρ := ρ) n hS hcont hnext yNext eNext

set_option linter.style.longLine false in
/-- The explicit selected-entry retained-passive datum itself has
residual-factor product equal to the selected-entry center-coordinate matrix.

This is the datum-level version of
`case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix`.
It removes only the `sourceReadback (edgeMatrix data)` wrapper by unfolding
the explicit datum's `C` field. -/
theorem case2PostPivotSelectedEntryRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
    {ρ : Type*} {τ : Type} [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    ChartLocalSuffixState.residualFactorProduct
        (case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext yNext eNext).C
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
  simpa [case2PostPivotSelectedEntryRetainedPassiveData,
    case2PostPivotRetainedPassiveData, case2SuccessorSelectedEntryMatrix] using
    residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_successorSelectedEntrySource_eq
      n hS hcont hnext yNext eNext

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- Endpoint-transported form of the explicit Case 2 retained-passive datum's
stored residual-factor selected-entry matrix readout. -/
theorem case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    [∀ q, Fintype (κ' q)] [∀ q, DecidableEq (κ' q)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    ChartLocalSuffixState.residualFactorProduct
        ((case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e).C
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ↦
          SelectedEntrySignedBox.CenterCoord.chartMap
            (⟨(J + 2, J + 2),
              case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
              {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)})
            yNext
            (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) (e (Fin.last 2)).symm
              ((e 0).symm.trans eNext) c)) := by
  have htransport :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.residualFactorProduct_C_endpointTransport
      (K := ℝ) (ρ := ρ)
      (e := e)
      (data := case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext)
      (i := 0) (j := Fin.last 2) (Fin.zero_le (Fin.last 2))
  have hbase :=
    case2PostPivotSelectedEntryRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
      (ρ := ρ) n hS hcont hnext yNext eNext
  rw [htransport, hbase]
  rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- Endpoint-transported residual readout for the passive-parameter selected-
entry retained-passive datum.

The conclusion is independent of the supplied passive variables: only the
stored residual `C` factors feed the selected-entry center-coordinate matrix.
This is finite coordinate algebra, not a measure pushforward or coverage
theorem. -/
theorem case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    [∀ q, Fintype (κ' q)] [∀ q, DecidableEq (κ' q)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (A1passive : Fin 1 → Matrix ρ ρ ℝ)
    (F2 : ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ)
    (A3passive : ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ)
    (Ctop : Matrix ρ ρ ℝ)
    (F3 : Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ)
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    ChartLocalSuffixState.residualFactorProduct
        ((case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
          (ρ := ρ) n hS hcont hnext A1passive F2 A3passive Ctop F3
          yNext eNext).endpointTransport e).C
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c : AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ↦
          SelectedEntrySignedBox.CenterCoord.chartMap
            (⟨(J + 2, J + 2),
              case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
              {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)})
            yNext
            (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) (e (Fin.last 2)).symm
              ((e 0).symm.trans eNext) c)) := by
  simpa [case2PostPivotSelectedEntryRetainedPassiveDataWithPassive,
    case2PostPivotSelectedEntryRetainedPassiveData,
    case2PostPivotRetainedPassiveData] using
    case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
      (ρ := ρ) n hS hcont hnext yNext eNext e

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- The endpoint-transported explicit Case 2 selected-entry datum has the
displayed successor pivot as the actual selected-entry product coordinate. -/
theorem case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_fixedPivot_entry_eq_yNext
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    [∀ q, Fintype (κ' q)] [∀ q, DecidableEq (κ' q)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    let pivotNext :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩
    let residualCoordEquiv :
        AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ≃
          (case2ResidualBlockPivotEntries n S (J + 1) : Type) :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    AoyagiResidualBlockCoordinateIndex.value
        (ChartLocalSuffixState.residualFactorProduct
          ((case2PostPivotSelectedEntryRetainedPassiveData
            (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)))
        (residualCoordEquiv.symm pivotNext) =
      yNext pivotNext := by
  intro pivotNext residualCoordEquiv
  let product :=
    ChartLocalSuffixState.residualFactorProduct
      ((case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e).C
      (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))
  have hmatrix :
      product =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
              (residualCoordEquiv c)) := by
    simpa [product, pivotNext, residualCoordEquiv] using
      case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
        (ρ := ρ) n hS hcont hnext yNext eNext e
  calc
    AoyagiResidualBlockCoordinateIndex.value product
        (residualCoordEquiv.symm pivotNext) =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
          (residualCoordEquiv (residualCoordEquiv.symm pivotNext)) := by
      rw [hmatrix]
      simpa using
        congrFun
          (AoyagiResidualBlockCoordinateIndex.value_matrix
            (fun c : AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ↦
              SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
                (residualCoordEquiv c)))
          (residualCoordEquiv.symm pivotNext)
    _ = yNext pivotNext := by
      rw [Equiv.apply_symm_apply]
      exact SelectedEntrySignedBox.CenterCoord.chartMap_pivot pivotNext yNext

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- The endpoint-transported explicit Case 2 selected-entry datum has a
nonzero fixed successor-pivot product coordinate when the supplied successor
pivot coordinate is nonzero. -/
theorem case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_fixedPivot_entry_ne_zero_of_yNext_pivot_ne_zero
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    [∀ q, Fintype (κ' q)] [∀ q, DecidableEq (κ' q)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (hyNext :
      yNext (⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0) :
    let pivotNext :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} :=
      ⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩
    let residualCoordEquiv :
        AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ≃
          (case2ResidualBlockPivotEntries n S (J + 1) : Type) :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    AoyagiResidualBlockCoordinateIndex.value
        (ChartLocalSuffixState.residualFactorProduct
          ((case2PostPivotSelectedEntryRetainedPassiveData
            (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)))
        (residualCoordEquiv.symm pivotNext) ≠ 0 := by
  intro pivotNext residualCoordEquiv
  rw [
    case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_fixedPivot_entry_eq_yNext
      (ρ := ρ) n hS hcont hnext yNext eNext e]
  exact hyNext

set_option linter.style.longLine false in
/-- The post-pivot residual `C 1` factor of the endpoint-transported explicit
Case 2 selected-entry retained-passive datum is the displayed post-pivot
residual block after reindexing back by the forward endpoint equivalences. -/
theorem case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_one_submatrix_eq_displayedPostPivotResidualBlock
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    (show Matrix (κ' (Fin.last 2)) (κ' (1 : Fin 3)) ℝ from
      by
        simpa using
          ((case2PostPivotSelectedEntryRetainedPassiveData
            (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e).C
            (1 : Fin 2)).submatrix (e (Fin.last 2)) (e (1 : Fin 3)) =
      case2DisplayedPostPivotResidualBlock n hS hcont
        (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext) := by
  change
    (((case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext yNext eNext).C
        (1 : Fin 2)).submatrix (e (Fin.last 2)).symm (e (1 : Fin 3)).symm).submatrix
      (e (Fin.last 2)) (e (1 : Fin 3)) =
      case2DisplayedPostPivotResidualBlock n hS hcont
        (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
  have hcancel :=
    matrix_submatrix_equiv_symm_submatrix_equiv
      ((case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext).C (1 : Fin 2))
      (e (Fin.last 2)) (e (1 : Fin 3))
  have hbase :
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext).C (1 : Fin 2) =
        case2DisplayedPostPivotResidualBlock n hS hcont
          (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext) := by
    change
      case2PostPivotFreeTwoEdgeFactorFamily n hS hcont
          (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
          (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext)
          (1 : Fin 2) =
        case2DisplayedPostPivotResidualBlock n hS hcont
          (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
    rfl
  exact hcancel.trans hbase

set_option linter.style.longLine false in
/-- The free-following `C 0` factor of the endpoint-transported explicit Case 2
selected-entry retained-passive datum is the displayed free following factor
after reindexing back by the forward endpoint equivalences. -/
theorem case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    (show Matrix (κ' (1 : Fin 3)) (κ' 0) ℝ from
      by
        simpa using
          ((case2PostPivotSelectedEntryRetainedPassiveData
            (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e).C
            (0 : Fin 2)).submatrix (e (1 : Fin 3)) (e 0) =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont
        (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext) := by
  change
    (((case2PostPivotSelectedEntryRetainedPassiveData
          (ρ := ρ) n hS hcont hnext yNext eNext).C
        (0 : Fin 2)).submatrix (e (1 : Fin 3)).symm (e 0).symm).submatrix
      (e (1 : Fin 3)) (e 0) =
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont
        (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext)
  have hcancel :=
    matrix_submatrix_equiv_symm_submatrix_equiv
      ((case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext).C (0 : Fin 2))
      (e (1 : Fin 3)) (e 0)
  have hbase :
      (case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext).C (0 : Fin 2) =
        case2DisplayedPostPivotFreeFollowingFactor n hS hcont
          (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext) := by
    change
      case2PostPivotFreeTwoEdgeFactorFamily n hS hcont
          (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
          (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext)
          (0 : Fin 2) =
        case2DisplayedPostPivotFreeFollowingFactor n hS hcont
          (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext)
    rfl
  exact hcancel.trans hbase

set_option linter.style.longLine false in
/-- The explicit selected-entry source readback's residual-factor product has
square-sum equal to the selected-entry center residual.

This is a pre-handoff algebraic readout.  It does not identify the explicit
Case 2 source family with a fixed-base p.13 source chart. -/
theorem aoyagiCoordinateSquareSum_case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenter_residual
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1)) :
    aoyagiCoordinateSquareSum
        (AoyagiResidualBlockCoordinateIndex.value
          (ChartLocalSuffixState.residualFactorProduct
            (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
              (K := ℝ) (ρ := ρ)
              (case2PostPivotSelectedEntrySourceEdgeFamily
                (ρ := ρ) n hS hcont hnext yNext eNext)).C
            (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)))) =
      SelectedEntrySignedBox.CenterCoord.residual
        (⟨(J + 2, J + 2),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)})
        yNext := by
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
  let product :=
    ChartLocalSuffixState.residualFactorProduct
      (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
        (K := ℝ) (ρ := ρ)
        (case2PostPivotSelectedEntrySourceEdgeFamily
          (ρ := ρ) n hS hcont hnext yNext eNext)).C
      (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))
  have hmatrix :
      product =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex
              (Case2ResidualRowIndex n S (J + 1)) τ ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
              (residualCoordEquiv c)) := by
    simpa [product, pivotNext, residualCoordEquiv] using
      case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
        (ρ := ρ) n hS hcont hnext yNext eNext
  have hcoord :
      AoyagiResidualBlockCoordinateIndex.value product =
        fun c : AoyagiResidualBlockCoordinateIndex
            (Case2ResidualRowIndex n S (J + 1)) τ ↦
          SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
            (residualCoordEquiv c) := by
    funext c
    have hmatrix_c :
        (AoyagiResidualBlockCoordinateIndex.value product) c =
          (AoyagiResidualBlockCoordinateIndex.value
            (AoyagiResidualBlockCoordinateIndex.matrix
              (fun c : AoyagiResidualBlockCoordinateIndex
                  (Case2ResidualRowIndex n S (J + 1)) τ ↦
                SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
                  (residualCoordEquiv c)))) c := by
      rw [hmatrix]
      rfl
    have hvalue_c :
        (AoyagiResidualBlockCoordinateIndex.value
          (AoyagiResidualBlockCoordinateIndex.matrix
            (fun c : AoyagiResidualBlockCoordinateIndex
                (Case2ResidualRowIndex n S (J + 1)) τ ↦
              SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
                (residualCoordEquiv c)))) c =
          SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
            (residualCoordEquiv c) := by
      simpa using congrFun
        (AoyagiResidualBlockCoordinateIndex.value_matrix
          (fun c : AoyagiResidualBlockCoordinateIndex
              (Case2ResidualRowIndex n S (J + 1)) τ ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
              (residualCoordEquiv c))) c
    exact hmatrix_c.trans hvalue_c
  calc
    aoyagiCoordinateSquareSum (AoyagiResidualBlockCoordinateIndex.value product) =
        aoyagiCoordinateSquareSum
          (fun c : AoyagiResidualBlockCoordinateIndex
              (Case2ResidualRowIndex n S (J + 1)) τ ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
              (residualCoordEquiv c)) := by
      rw [hcoord]
      rfl
    _ = aoyagiCoordinateSquareSum
          (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext) :=
      aoyagiCoordinateSquareSum_comp_equiv residualCoordEquiv
        (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext)
    _ = SelectedEntrySignedBox.CenterCoord.residual pivotNext yNext :=
      (SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap
        pivotNext yNext).symm

set_option linter.style.longLine false in
/-- The explicit selected-entry source edge family's readback product is
nonzero when the displayed successor selected-entry pivot coordinate is
nonzero. -/
theorem case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_ne_zero_of_yNext_pivot_ne_zero
    {ρ : Type*} {τ : Type} [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ]
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
    ChartLocalSuffixState.residualFactorProduct
        (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
          (K := ℝ) (ρ := ρ)
          (case2PostPivotSelectedEntrySourceEdgeFamily
            (ρ := ρ) n hS hcont hnext yNext eNext)).C
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) ≠ 0 := by
  rw [
    case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix
      (ρ := ρ) n hS hcont hnext yNext eNext]
  exact
    case2SuccessorSelectedEntryMatrix_ne_zero_of_yNext_pivot_ne_zero
      n hS hnext yNext eNext hyNext

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
/-- The endpoint-transported explicit Case 2 selected-entry retained-passive
datum satisfies the all-pivot selected-entry residual-product readout once the
displayed two-edge product is nonzero.

The two displayed factor identities are discharged by the explicit datum's
endpoint-transport factor-alignment lemmas.  The product nonzeroness hypothesis
remains supplied. -/
theorem exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_ne_zero
    {ρ ι : Type*} {τ : Type} [DecidableEq ρ] [DecidableEq ι]
    {κ' : Fin 3 → Type*} [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {center : Finset ι}
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ≃ center)
    (hprod :
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont
        (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
        (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext) ≠ 0) :
    ∃ pivot : center, ∃ y : center → ℝ,
      ChartLocalSuffixState.residualFactorProduct
          ((case2PostPivotSelectedEntryRetainedPassiveData
            (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c)) := by
  exact
    exists_pivot_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero
      (ρ := ρ) (τ := τ) (ι := ι) (κ := κ') (center := center)
      n hS hcont
      (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
      (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext)
      ((case2PostPivotSelectedEntryRetainedPassiveData
        (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e)
      residualCoordEquiv (e (Fin.last 2)) (e (1 : Fin 3)) (e 0)
      (case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_one_submatrix_eq_displayedPostPivotResidualBlock
        (ρ := ρ) n hS hcont hnext yNext eNext e)
      (case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor
        (ρ := ρ) n hS hcont hnext yNext eNext e)
      hprod

set_option linter.style.longLine false in
/-- The endpoint-transported explicit Case 2 selected-entry retained-passive
datum satisfies the all-pivot selected-entry residual-product readout when the
successor selected-entry pivot coordinate is nonzero.

This discharges the displayed-product nonzeroness input of
`exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_ne_zero`
for the constructed successor source residual and free `Cprime`.  The
conclusion is all-pivot/existential: it does not identify the produced pivot
with `(J + 2, J + 2)` or the produced coordinates with the supplied `yNext`. -/
theorem exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_yNext_pivot_ne_zero
    {ρ ι : Type*} {τ : Type} [DecidableEq ρ] [DecidableEq ι]
    {κ' : Fin 3 → Type*} [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {center : Finset ι}
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (yNext :
      {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)} → ℝ)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ≃ center)
    (hyNext :
      yNext (⟨(J + 2, J + 2),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
        {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0) :
    ∃ pivot : center, ∃ y : center → ℝ,
      ChartLocalSuffixState.residualFactorProduct
          ((case2PostPivotSelectedEntryRetainedPassiveData
            (ρ := ρ) n hS hcont hnext yNext eNext).endpointTransport e).C
          (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex (κ' (Fin.last 2)) (κ' 0) ↦
            SelectedEntrySignedBox.CenterCoord.chartMap pivot y
              (residualCoordEquiv c)) := by
  have hprod :
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont
        (case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext)
        (case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext) ≠ 0 := by
    rw [
      case2DisplayedPostPivotFreeTwoEdgeFactorProduct_successorSelectedEntrySource_eq
        n hS hcont hnext yNext eNext]
    exact
      case2SuccessorSelectedEntryMatrix_ne_zero_of_yNext_pivot_ne_zero
        n hS hnext yNext eNext hyNext
  exact
    exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_ne_zero
      (ρ := ρ) (τ := τ) (ι := ι) (κ' := κ') (center := center)
      n hS hcont hnext yNext eNext e residualCoordEquiv hprod

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
