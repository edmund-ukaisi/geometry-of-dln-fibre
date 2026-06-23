import DLNFibre.DLN.Aoyagi.Case2FiniteExponentBridge

/-!
# Selected-entry finite normal-crossing microcertificate

This file turns the elementary selected-entry square-sum and formal determinant
calculation into a one-chart `AoyagiNormalCrossingChartCertificate`.  The
certificate is deliberately local: its loss is only the finite center
square-sum, and its Jacobian/prior factor is only the formal pivot-first
determinant.  It does not prove chart coverage, analytic regularity, a
volume-form theorem, source production, or RLCT extraction.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

open scoped BigOperators
open Case2DisplayedSuppliedChartFamilyBoundary

/-- Extend the non-pivot residual coordinates of a finite selected-entry chart
to an ambient function so the existing selected-entry square-sum lemma can be
reused.  Values outside the erased center are irrelevant to the certificate. -/
private def selectedEntryErasedResidual
    {ι K : Type*} [DecidableEq ι] [Zero K]
    {center : Finset ι} (pivot : center)
    (residual : (center.erase pivot.1 : Finset ι) → K) : ι → K :=
  fun i ↦ if h : i ∈ center.erase pivot.1 then residual ⟨i, h⟩ else 0

/-- One-chart finite normal-crossing certificate for the selected-entry
square-sum and formal pivot-first determinant.

The parameter is a value function on the finite center subtype.  The single
chart uses coordinates `(u, residual)` with `x_p = u` and `x_i = u *
residual_i` on the non-pivot entries inside that finite center.  The loss is
the finite center square-sum, and the Jacobian/prior factor is the formal
determinant `u^(|center \ {p}|)`.

This is not an analytic chart-production or Jacobian theorem. -/
def selectedEntryCenterSqFormalJacobianChartCertificate
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center) :
    AoyagiNormalCrossingChartCertificate (center → K) K where
  numCharts := 1
  numCoords := 1
  ChartPoint := fun _ ↦ K × ((center.erase pivot.1 : Finset ι) → K)
  chartPoint_nonempty := fun _ ↦ ⟨(0, fun _ ↦ 0)⟩
  chartMap := fun _ x i ↦
    selectedEntryChartMap pivot.1 x.1
      (selectedEntryErasedResidual pivot x.2) i.1
  coord := fun _ x _ ↦ x.1
  loss := fun value ↦ selectedEntryCenterSq (Finset.univ : Finset center) value
  jacobianPrior := fun _ x ↦ x.1 ^ (center.erase pivot.1).card
  lossUnit := fun _ x ↦
    selectedEntryCenterSqUnitFactor (center.erase pivot.1)
      (selectedEntryErasedResidual pivot x.2)
  jacobianPriorUnit := fun _ _ ↦ 1
  lossExp := fun _ _ ↦ 1
  jacobianPriorExp := fun _ _ ↦ (center.erase pivot.1).card
  loss_monomial := by
    intro c x
    have hcenter :
        selectedEntryCenterSq (Finset.univ : Finset center)
            (fun i ↦ selectedEntryChartMap pivot.1 x.1
              (selectedEntryErasedResidual pivot x.2) i.1) =
          selectedEntryCenterSq center
            (selectedEntryChartMap pivot.1 x.1
              (selectedEntryErasedResidual pivot x.2)) := by
      simpa [selectedEntryCenterSq] using
        (Finset.sum_attach center
          (fun i ↦ selectedEntryChartMap pivot.1 x.1
            (selectedEntryErasedResidual pivot x.2) i ^ 2))
    rw [hcenter]
    rw [selectedEntryCenterSq_selectedEntryChartMap pivot.2 x.1
      (selectedEntryErasedResidual pivot x.2)]
    simp [selectedEntryCenterSqUnitFactor]
    ring
  jacobianPrior_monomial := by
    intro c x
    simp
  lossUnit_isUnit := by
    intro c x
    exact selectedEntryCenterSqUnitFactor_isUnit (center.erase pivot.1)
      (selectedEntryErasedResidual pivot x.2)
  jacobianPriorUnit_isUnit := by
    intro c x
    exact isUnit_one
  active_nonempty := by
    exact ⟨((0 : Fin 1), (0 : Fin 1)), by simp⟩

namespace selectedEntryCenterSqFormalJacobianChartCertificate

/-- The unique coordinate has loss exponent `1`. -/
@[simp] theorem lossExp_zero_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).lossExp (0 : Fin 1) (0 : Fin 1) = 1 :=
  rfl

/-- The unique coordinate has formal Jacobian/prior exponent
`|center \ {pivot}|`. -/
@[simp] theorem jacobianPriorExp_zero_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).jacobianPriorExp (0 : Fin 1) (0 : Fin 1) =
      (center.erase pivot.1).card :=
  rfl

/-- The unique coordinate has finite exponent ratio `|center| / 2`. -/
theorem exponentData_ratioAt_zero_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData.ratioAt ((0 : Fin 1), (0 : Fin 1)) =
      (center.card : ℚ) / 2 := by
  let D :=
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData
  have hloss : D.lossExp (0 : Fin 1) (0 : Fin 1) = 1 := rfl
  have hjac : D.jacobianPriorExp (0 : Fin 1) (0 : Fin 1) + 1 =
      center.card := by
    exact Finset.card_erase_add_one pivot.2
  exact D.ratioAt_eq_nat_div_two_of_lossExp_eq_one_of_jacobianPriorExp_add_one_eq
    hloss hjac

/-- The one-coordinate finite exponent minimum of the local selected-entry
microcertificate is `|center| / 2`. -/
theorem exponentData_exponentMinimum_eq_centerCard_div_two
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData.exponentMinimum =
      (center.card : ℚ) / 2 := by
  let D :=
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData
  have hratio :
      D.ratioAt ((0 : Fin 1), (0 : Fin 1)) =
        (center.card : ℚ) / 2 :=
    exponentData_ratioAt_zero_zero (K := K) pivot
  refine D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
    (D.mem_activePairs_of_lossExp_eq_one (by rfl)) hratio ?_
  intro p hp
  rcases p with ⟨c, j⟩
  fin_cases c
  fin_cases j
  exact le_of_eq (by simpa using hratio.symm)

/-- In the local one-coordinate selected-entry microcertificate, every chart
has at most one coordinate attaining the finite exponent minimum. -/
theorem exponentData_minCountInChart_le_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (c :
      Fin (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) pivot).exponentData.numCharts) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData.minCountInChart c ≤ 1 := by
  let D :=
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData
  rw [AoyagiNormalCrossingExponentData.minCountInChart,
    AoyagiNormalCrossingExponentData.minCoordsInChart]
  refine le_trans (Finset.card_filter_le _ _) ?_
  change (Finset.univ : Finset (Fin 1)).card ≤ 1
  simp

/-- The local one-coordinate selected-entry microcertificate has finite
exponent order `1`. -/
theorem exponentData_exponentOrder_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData.exponentOrder = 1 := by
  let D :=
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData
  apply le_antisymm
  · rcases D.exists_chart_minCount_eq_exponentOrder with ⟨c, hc⟩
    rw [← hc]
    exact exponentData_minCountInChart_le_one (K := K) pivot c
  · exact D.one_le_exponentOrder

end selectedEntryCenterSqFormalJacobianChartCertificate

/-- Case 2 specialization of the selected-entry finite normal-crossing
microcertificate at Aoyagi's displayed pivot `(J+1,J+1)`.

The certificate covers only the finite residual-block center square-sum and
formal selected-entry determinant for this chart.  It is not the global
normal-crossing chart family for the DLN loss. -/
def case2DisplayedCenterSqFormalJacobianChartCertificate
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AoyagiNormalCrossingChartCertificate
      ({p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J} → K) K :=
  selectedEntryCenterSqFormalJacobianChartCertificate
    (ι := ℕ × ℕ)
    (K := K)
    (center := case2ResidualBlockPivotEntries n S J)
    ⟨(J + 1, J + 1),
      case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont⟩

namespace case2DisplayedCenterSqFormalJacobianChartCertificate

/-- The unique coordinate in the Case 2 finite microcertificate has loss
exponent `1`. -/
@[simp] theorem lossExp_zero_zero
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).lossExp (0 : Fin 1) (0 : Fin 1) = 1 :=
  rfl

/-- The unique coordinate in the Case 2 finite microcertificate has formal
Jacobian/prior exponent equal to the number of non-pivot residual-block center
coordinates. -/
@[simp] theorem jacobianPriorExp_zero_zero
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).jacobianPriorExp (0 : Fin 1) (0 : Fin 1) =
      ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1)).card :=
  rfl

/-- The unique coordinate in the Case 2 finite microcertificate has finite
exponent ratio equal to half the residual-block center cardinality. -/
theorem exponentData_ratioAt_zero_zero
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData.ratioAt
        ((0 : Fin 1), (0 : Fin 1)) =
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 :=
  selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero
    (K := K)
    ⟨(J + 1, J + 1),
      case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont⟩

/-- The finite exponent minimum of the Case 2 local microcertificate is half
the residual-block center cardinality. -/
theorem exponentData_exponentMinimum_eq_centerCard_div_two
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData.exponentMinimum =
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 := by
  let D :=
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData
  have hratio :
      D.ratioAt ((0 : Fin 1), (0 : Fin 1)) =
        ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 :=
    exponentData_ratioAt_zero_zero (K := K) n hS hcont
  refine D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
    (D.mem_activePairs_of_lossExp_eq_one (by rfl)) hratio ?_
  intro p hp
  rcases p with ⟨c, j⟩
  fin_cases c
  fin_cases j
  exact le_of_eq (by simpa using hratio.symm)

/-- The Case 2 local one-coordinate microcertificate has finite exponent
order `1`. -/
theorem exponentData_exponentOrder_eq_one
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData.exponentOrder = 1 := by
  let D :=
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData
  apply le_antisymm
  · rcases D.exists_chart_minCount_eq_exponentOrder with ⟨c, hc⟩
    rw [← hc]
    rw [AoyagiNormalCrossingExponentData.minCountInChart,
      AoyagiNormalCrossingExponentData.minCoordsInChart]
    refine le_trans (Finset.card_filter_le _ _) ?_
    change (Finset.univ : Finset (Fin 1)).card ≤ 1
    simp
  · exact D.one_le_exponentOrder

/-- The Case 2 finite microcertificate supplies the exponent-coordinate bridge
for its own one-coordinate exponent data.

This does not identify the microcertificate with the full A0 chart family for
the DLN loss, and it does not prove any global active-ratio lower bound. -/
theorem localExponentCoordinateBridge
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {C : ℕ → τ → K}
    (cert :
      Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
        L n S J t numerator leastValue pre u residual hS hcont C) :
    Case2DisplayedContinuingA0ExponentCoordinateBridge cert
      (case2DisplayedCenterSqFormalJacobianChartCertificate
        (K := K) n hS hcont).exponentData
      ((0 : Fin 1), (0 : Fin 1)) where
  lossExp_eq_one := rfl
  jacobianPriorExp_eq_formalPivotExp := rfl

end case2DisplayedCenterSqFormalJacobianChartCertificate

end Aoyagi
end DLN
end DLNFibre
