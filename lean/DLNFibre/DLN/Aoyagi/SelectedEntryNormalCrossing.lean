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

/-- The point of the generic selected-entry microcertificate corresponding to
ambient selected-entry source coordinates `(u, residual)`. -/
def sourceChartPoint
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).ChartPoint (0 : Fin 1) :=
  (u, fun p ↦ residual p.1)

/-- The generic selected-entry microcertificate chart map agrees with the
ambient selected-entry source chart map at `sourceChartPoint`. -/
theorem chartMap_sourceChartPoint_eq
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).chartMap (0 : Fin 1)
        (sourceChartPoint pivot u residual) =
      fun i : center ↦ selectedEntryChartMap pivot.1 u residual i.1 := by
  funext i
  by_cases hi : i.1 = pivot.1
  · simp [sourceChartPoint, selectedEntryCenterSqFormalJacobianChartCertificate,
      selectedEntryChartMap, hi]
  · have hmem : i.1 ∈ center.erase pivot.1 := by
      simp [Finset.mem_erase, hi, i.2]
    simp [sourceChartPoint, selectedEntryCenterSqFormalJacobianChartCertificate,
      selectedEntryChartMap, selectedEntryErasedResidual, hi, hmem]

/-- If the selected pivot coordinate of a finite center value is nonzero, the
one-pivot selected-entry chart has a preimage of that value.

This is finite map coverage for the selected-entry formula only; it does not
prove analytic chart coverage or transition regularity. -/
theorem exists_oneChartPoint_chartMap_eq_value_of_pivot_ne_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (value : center → K) (hpivot : value pivot ≠ 0) :
    ∃ x :
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) pivot).ChartPoint (0 : Fin 1),
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) pivot).chartMap (0 : Fin 1) x = value := by
  let residual : ι → K :=
    fun i ↦ if h : i ∈ center then value ⟨i, h⟩ / value pivot else 0
  refine ⟨sourceChartPoint pivot (value pivot) residual, ?_⟩
  rw [chartMap_sourceChartPoint_eq]
  funext i
  by_cases hi : i.1 = pivot.1
  · cases Subtype.ext hi
    simp [selectedEntryChartMap]
  · have hmem : i.1 ∈ center := i.2
    simp [selectedEntryChartMap, hi, residual, hmem]
    field_simp [hpivot]

/-- If a finite center value is identically zero, every one-pivot
selected-entry chart has a zero chart point over it.

This is finite map coverage for the selected-entry formula only; it does not
prove analytic chart coverage or transition regularity. -/
theorem exists_oneChartPoint_chartMap_eq_value_of_forall_eq_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (value : center → K) (hzero : ∀ i, value i = 0) :
    ∃ x :
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) pivot).ChartPoint (0 : Fin 1),
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) pivot).chartMap (0 : Fin 1) x = value := by
  refine ⟨sourceChartPoint pivot 0 (fun _ ↦ 0), ?_⟩
  rw [chartMap_sourceChartPoint_eq]
  funext i
  rw [hzero i]
  simp [selectedEntryChartMap]

/-- At the generic selected-entry source chart point, the microcertificate
loss is the finite center square-sum. -/
theorem loss_sourceChartPoint_eq_centerSq
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).loss
        ((selectedEntryCenterSqFormalJacobianChartCertificate
          (K := K) pivot).chartMap (0 : Fin 1)
            (sourceChartPoint pivot u residual)) =
      selectedEntryCenterSq center
        (selectedEntryChartMap pivot.1 u residual) := by
  rw [chartMap_sourceChartPoint_eq]
  simpa [selectedEntryCenterSqFormalJacobianChartCertificate, selectedEntryCenterSq] using
    (Finset.sum_attach center
      (fun i ↦ selectedEntryChartMap pivot.1 u residual i ^ 2))

/-- At the generic selected-entry source chart point, the microcertificate
loss unit is the normalized finite center-square factor. -/
theorem lossUnit_sourceChartPoint_eq
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).lossUnit (0 : Fin 1)
        (sourceChartPoint pivot u residual) =
      selectedEntryCenterSqUnitFactor (center.erase pivot.1) residual := by
  simp only [sourceChartPoint, selectedEntryCenterSqFormalJacobianChartCertificate]
  rw [selectedEntryCenterSqUnitFactor, selectedEntryCenterSqUnitFactor]
  congr 1
  rw [selectedEntryCenterSq, selectedEntryCenterSq]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hmem : i ∈ center.erase pivot.1 := hi
  simp [selectedEntryErasedResidual, hmem]

/-- At the generic selected-entry source chart point, the microcertificate
Jacobian/prior value is the formal pivot-first determinant. -/
theorem jacobianPrior_sourceChartPoint_eq_det
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).jacobianPrior (0 : Fin 1)
        (sourceChartPoint pivot u residual) =
      (selectedEntryPivotFirstJacobian
        (κ := {i // i ∈ center.erase pivot.1}) u
        (fun p ↦ residual p.1)).det := by
  rw [selectedEntryPivotFirstJacobian_det]
  simp [sourceChartPoint, selectedEntryCenterSqFormalJacobianChartCertificate,
    Fintype.card_coe]

/-- Source-chart presentation of the generic selected-entry loss monomial
identity. -/
theorem loss_monomial_sourceChartPoint
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (u : K) (residual : ι → K) :
    selectedEntryCenterSq center (selectedEntryChartMap pivot.1 u residual) =
      selectedEntryCenterSqUnitFactor (center.erase pivot.1) residual *
        ∏ j : Fin (selectedEntryCenterSqFormalJacobianChartCertificate
            (K := K) pivot).numCoords,
          (selectedEntryCenterSqFormalJacobianChartCertificate
            (K := K) pivot).coord (0 : Fin 1)
            (sourceChartPoint pivot u residual) j ^
            (2 *
              (selectedEntryCenterSqFormalJacobianChartCertificate
                (K := K) pivot).lossExp (0 : Fin 1) j) := by
  rw [← loss_sourceChartPoint_eq_centerSq pivot u residual]
  rw [← lossUnit_sourceChartPoint_eq pivot u residual]
  exact
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).loss_monomial
        (0 : Fin 1) (sourceChartPoint pivot u residual)

/-- Source-chart presentation of the generic selected-entry formal
Jacobian/prior monomial identity. -/
theorem jacobianPrior_monomial_sourceChartPoint
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (u : K) (residual : ι → K) :
    (selectedEntryPivotFirstJacobian
        (κ := {i // i ∈ center.erase pivot.1}) u
        (fun p ↦ residual p.1)).det =
      (selectedEntryCenterSqFormalJacobianChartCertificate
          (K := K) pivot).jacobianPriorUnit (0 : Fin 1)
          (sourceChartPoint pivot u residual) *
        ∏ j : Fin (selectedEntryCenterSqFormalJacobianChartCertificate
            (K := K) pivot).numCoords,
          (selectedEntryCenterSqFormalJacobianChartCertificate
            (K := K) pivot).coord (0 : Fin 1)
            (sourceChartPoint pivot u residual) j ^
            (selectedEntryCenterSqFormalJacobianChartCertificate
              (K := K) pivot).jacobianPriorExp (0 : Fin 1) j := by
  rw [← jacobianPrior_sourceChartPoint_eq_det pivot u residual]
  exact
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).jacobianPrior_monomial
        (0 : Fin 1) (sourceChartPoint pivot u residual)

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

/-- In the local one-coordinate selected-entry microcertificate, the chart
count at the local ratio `|center| / 2` is `1`. -/
theorem exponentData_countInChartAtRatio_centerCard_div_two_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (c :
      Fin (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) pivot).exponentData.numCharts) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData.countInChartAtRatio
        ((center.card : ℚ) / 2) c = 1 := by
  let D :=
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData
  fin_cases c
  rw [AoyagiNormalCrossingExponentData.countInChartAtRatio,
    AoyagiNormalCrossingExponentData.coordsInChartAtRatio]
  change
    ((Finset.univ : Finset (Fin 1)).filter
      (fun j ↦
        0 < D.lossExp (0 : Fin 1) j ∧
          D.ratioAt ((0 : Fin 1), j) = (center.card : ℚ) / 2)).card = 1
  have hfilter :
      ((Finset.univ : Finset (Fin 1)).filter
        (fun j ↦
          0 < D.lossExp (0 : Fin 1) j ∧
            D.ratioAt ((0 : Fin 1), j) = (center.card : ℚ) / 2)) =
        Finset.univ := by
    apply Finset.filter_true_of_mem
    intro j _hj
    fin_cases j
    exact ⟨by simp [D, selectedEntryCenterSqFormalJacobianChartCertificate],
      by simpa [D] using exponentData_ratioAt_zero_zero (K := K) pivot⟩
  rw [hfilter]
  change (Finset.univ : Finset (Fin 1)).card = 1
  simp

private theorem countAtLocalRatio_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (c :
      Fin (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) pivot).exponentData.numCharts) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData.countInChartAtRatio
        ((center.card : ℚ) / 2) c = 1 :=
  exponentData_countInChartAtRatio_centerCard_div_two_eq_one (K := K) pivot c

/-- In the local one-coordinate selected-entry microcertificate, the
chartwise minimum-coordinate count is `1`. -/
theorem exponentData_minCountInChart_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (pivot : center)
    (c :
      Fin (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) pivot).exponentData.numCharts) :
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData.minCountInChart c = 1 := by
  let D :=
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) pivot).exponentData
  rw [D.minCountInChart_eq_countInChartAtRatio_of_exponentMinimum_eq
    (exponentData_exponentMinimum_eq_centerCard_div_two (K := K) pivot) c]
  exact exponentData_countInChartAtRatio_centerCard_div_two_eq_one (K := K) pivot c

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

/-- Finite all-pivot chart-family certificate for the selected-entry
square-sum and formal pivot-first determinant.

The charts are indexed by a supplied equivalence from `Fin center.card` to the
finite center subtype.  Chart `c` is exactly the existing one-pivot
selected-entry certificate for the pivot `chartEquiv c`.  This is finite
certificate bookkeeping only: it does not prove atlas coverage, transition
regularity, analytic Jacobian control, or source production. -/
def selectedEntryCenterSqFormalJacobianChartFamilyCertificate
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    AoyagiNormalCrossingChartCertificate (center → K) K where
  numCharts := center.card
  numCoords := 1
  ChartPoint := fun c ↦
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) (chartEquiv c)).ChartPoint (0 : Fin 1)
  chartPoint_nonempty := fun c ↦
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) (chartEquiv c)).chartPoint_nonempty (0 : Fin 1)
  chartMap := fun c x ↦
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) (chartEquiv c)).chartMap (0 : Fin 1) x
  coord := fun c x ↦
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) (chartEquiv c)).coord (0 : Fin 1) x
  loss := fun value ↦ selectedEntryCenterSq (Finset.univ : Finset center) value
  jacobianPrior := fun c x ↦
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) (chartEquiv c)).jacobianPrior (0 : Fin 1) x
  lossUnit := fun c x ↦
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) (chartEquiv c)).lossUnit (0 : Fin 1) x
  jacobianPriorUnit := fun c x ↦
    (selectedEntryCenterSqFormalJacobianChartCertificate
      (K := K) (chartEquiv c)).jacobianPriorUnit (0 : Fin 1) x
  lossExp := fun _ _ ↦ 1
  jacobianPriorExp := fun c _ ↦ (center.erase (chartEquiv c).1).card
  loss_monomial := by
    intro c x
    simpa [selectedEntryCenterSqFormalJacobianChartCertificate] using
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) (chartEquiv c)).loss_monomial (0 : Fin 1) x
  jacobianPrior_monomial := by
    intro c x
    simp [selectedEntryCenterSqFormalJacobianChartCertificate]
  lossUnit_isUnit := by
    intro c x
    exact
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) (chartEquiv c)).lossUnit_isUnit (0 : Fin 1) x
  jacobianPriorUnit_isUnit := by
    intro c x
    exact
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := K) (chartEquiv c)).jacobianPriorUnit_isUnit (0 : Fin 1) x
  active_nonempty := by
    rcases hcenter with ⟨p, hp⟩
    exact ⟨(chartEquiv.symm ⟨p, hp⟩, (0 : Fin 1)), by simp⟩

namespace selectedEntryCenterSqFormalJacobianChartFamilyCertificate

open selectedEntryCenterSqFormalJacobianChartCertificate

/-- Every chart in the selected-entry chart family has loss exponent `1` on
its unique monomial coordinate. -/
@[simp] theorem lossExp_chart_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).lossExp c (0 : Fin 1) = 1 :=
  rfl

/-- The formal Jacobian/prior exponent in chart `c` is the number of
non-pivot center entries for that chart. -/
@[simp] theorem jacobianPriorExp_chart_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).jacobianPriorExp c (0 : Fin 1) =
      (center.erase (chartEquiv c).1).card :=
  rfl

/-- In every chart, the unique active coordinate has finite ratio
`|center| / 2`. -/
theorem exponentData_ratioAt_chart_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData.ratioAt (c, (0 : Fin 1)) =
      (center.card : ℚ) / 2 := by
  let D :=
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData
  have hloss : D.lossExp c (0 : Fin 1) = 1 := rfl
  have hjac : D.jacobianPriorExp c (0 : Fin 1) + 1 = center.card := by
    exact Finset.card_erase_add_one (chartEquiv c).2
  exact D.ratioAt_eq_nat_div_two_of_lossExp_eq_one_of_jacobianPriorExp_add_one_eq
    hloss hjac

/-- The finite exponent minimum of the selected-entry all-pivot chart family
is `|center| / 2`. -/
theorem exponentData_exponentMinimum_eq_centerCard_div_two
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData.exponentMinimum =
      (center.card : ℚ) / 2 := by
  let C :=
    selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv
  let D := C.exponentData
  rcases hcenter with ⟨p, hp⟩
  let c0 : Fin center.card := chartEquiv.symm ⟨p, hp⟩
  have hratio :
      D.ratioAt (c0, (0 : Fin 1)) = (center.card : ℚ) / 2 := by
    exact exponentData_ratioAt_chart_zero (K := K)
      (hcenter := ⟨p, hp⟩) chartEquiv c0
  refine D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
    (D.mem_activePairs_of_lossExp_eq_one (by rfl)) hratio ?_
  intro p' hp'
  rcases p' with ⟨c, j⟩
  fin_cases j
  exact le_of_eq (by
    simpa [D] using
      (exponentData_ratioAt_chart_zero (K := K)
        (hcenter := ⟨p, hp⟩) chartEquiv c).symm)

/-- In every selected-entry pivot chart, the count at ratio `|center| / 2`
is `1`. -/
theorem exponentData_countInChartAtRatio_centerCard_div_two_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData.countInChartAtRatio
        ((center.card : ℚ) / 2) c = 1 := by
  let D :=
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData
  rw [AoyagiNormalCrossingExponentData.countInChartAtRatio,
    AoyagiNormalCrossingExponentData.coordsInChartAtRatio]
  change
    ((Finset.univ : Finset (Fin 1)).filter
      (fun j ↦
        0 < D.lossExp c j ∧
          D.ratioAt (c, j) = (center.card : ℚ) / 2)).card = 1
  have hfilter :
      ((Finset.univ : Finset (Fin 1)).filter
        (fun j ↦
          0 < D.lossExp c j ∧
            D.ratioAt (c, j) = (center.card : ℚ) / 2)) =
        Finset.univ := by
    apply Finset.filter_true_of_mem
    intro j _hj
    fin_cases j
    exact ⟨by simp [D, selectedEntryCenterSqFormalJacobianChartFamilyCertificate],
      by simpa [D] using
        exponentData_ratioAt_chart_zero (K := K) hcenter chartEquiv c⟩
  rw [hfilter]
  change (Finset.univ : Finset (Fin 1)).card = 1
  simp

private theorem countAtLocalRatio_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData.countInChartAtRatio
        ((center.card : ℚ) / 2) c = 1 :=
  exponentData_countInChartAtRatio_centerCard_div_two_eq_one
    (K := K) hcenter chartEquiv c

/-- In every selected-entry pivot chart, the chartwise minimum-coordinate
count is `1`. -/
theorem exponentData_minCountInChart_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData.minCountInChart c = 1 := by
  let D :=
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData
  rw [D.minCountInChart_eq_countInChartAtRatio_of_exponentMinimum_eq
    (exponentData_exponentMinimum_eq_centerCard_div_two (K := K) hcenter chartEquiv) c]
  exact exponentData_countInChartAtRatio_centerCard_div_two_eq_one
    (K := K) hcenter chartEquiv c

/-- The selected-entry all-pivot chart family has finite exponent order `1`. -/
theorem exponentData_exponentOrder_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData.exponentOrder = 1 := by
  let D :=
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData
  rcases hcenter with ⟨p, hp⟩
  let c0 : Fin center.card := chartEquiv.symm ⟨p, hp⟩
  refine D.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
    (exponentData_exponentMinimum_eq_centerCard_div_two (K := K)
      (hcenter := ⟨p, hp⟩) chartEquiv)
    (c := c0) ?_ ?_
  · exact exponentData_countInChartAtRatio_centerCard_div_two_eq_one
      (K := K) (hcenter := ⟨p, hp⟩) chartEquiv c0
  · intro c
    rw [exponentData_countInChartAtRatio_centerCard_div_two_eq_one
      (K := K) (hcenter := ⟨p, hp⟩) chartEquiv c]

/-- The source point of chart `c` in the all-pivot selected-entry chart
family, obtained by delegating to the one-pivot source point at the selected
pivot. -/
def sourceChartPoint
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).ChartPoint c :=
  selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint
    (chartEquiv c) u residual

/-- In chart `c`, the all-pivot family chart map at the source point is the
one-pivot selected-entry source chart map for the selected pivot. -/
theorem chartMap_sourceChartPoint_eq
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).chartMap c
        (sourceChartPoint hcenter chartEquiv c u residual) =
      fun i : center ↦ selectedEntryChartMap (chartEquiv c).1 u residual i.1 := by
  simpa [sourceChartPoint, selectedEntryCenterSqFormalJacobianChartFamilyCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.chartMap_sourceChartPoint_eq
        (chartEquiv c) u residual

/-- In a fixed chart of the all-pivot selected-entry family, a finite center
value whose selected pivot coordinate is nonzero has a preimage.

This is finite selected-entry map coverage only, not analytic atlas coverage. -/
theorem exists_chartPoint_chartMap_eq_value_of_chart_pivot_ne_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card)
    (value : center → K) (hpivot : value (chartEquiv c) ≠ 0) :
    ∃ x :
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv).ChartPoint c,
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv).chartMap c x = value := by
  simpa [selectedEntryCenterSqFormalJacobianChartFamilyCertificate] using
    exists_oneChartPoint_chartMap_eq_value_of_pivot_ne_zero
      (K := K) (chartEquiv c) value hpivot

/-- The all-pivot selected-entry family covers every finite center value.

If the value is zero, any pivot chart maps a zero chart point to it.  Otherwise
choose a nonzero coordinate as pivot and divide the other coordinates by it.
This is finite selected-entry map coverage only, not analytic atlas coverage,
transition regularity, source production, or normal-crossing extraction. -/
theorem exists_chartPoint_chartMap_eq_value
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (value : center → K) :
    ∃ c : Fin center.card,
      ∃ x :
        (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
          (K := K) hcenter chartEquiv).ChartPoint c,
        (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
          (K := K) hcenter chartEquiv).chartMap c x = value := by
  classical
  by_cases hzero : ∀ i : center, value i = 0
  · rcases hcenter with ⟨p, hp⟩
    let c : Fin center.card := chartEquiv.symm ⟨p, hp⟩
    refine ⟨c, ?_⟩
    simpa [c, selectedEntryCenterSqFormalJacobianChartFamilyCertificate] using
      exists_oneChartPoint_chartMap_eq_value_of_forall_eq_zero
        (K := K) (chartEquiv c) value hzero
  · have hnonzero : ∃ i : center, value i ≠ 0 := by
      by_contra hnone
      apply hzero
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    rcases hnonzero with ⟨p, hp⟩
    let c : Fin center.card := chartEquiv.symm p
    have hc : chartEquiv c = p := by simp [c]
    refine ⟨c, ?_⟩
    simpa [c, hc, selectedEntryCenterSqFormalJacobianChartFamilyCertificate] using
      exists_oneChartPoint_chartMap_eq_value_of_pivot_ne_zero
        (K := K) (chartEquiv c) value (by simpa [hc] using hp)

/-- At an all-pivot family source point, the finite loss is the selected-entry
center square in the selected pivot chart. -/
theorem loss_sourceChartPoint_eq_centerSq
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).loss
        ((selectedEntryCenterSqFormalJacobianChartFamilyCertificate
          (K := K) hcenter chartEquiv).chartMap c
            (sourceChartPoint hcenter chartEquiv c u residual)) =
      selectedEntryCenterSq center
        (selectedEntryChartMap (chartEquiv c).1 u residual) := by
  simpa [sourceChartPoint, selectedEntryCenterSqFormalJacobianChartFamilyCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.loss_sourceChartPoint_eq_centerSq
        (chartEquiv c) u residual

/-- At an all-pivot family source point, the loss unit is the selected pivot's
normalized finite center-square factor. -/
theorem lossUnit_sourceChartPoint_eq
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).lossUnit c
        (sourceChartPoint hcenter chartEquiv c u residual) =
      selectedEntryCenterSqUnitFactor
        (center.erase (chartEquiv c).1) residual := by
  simpa [sourceChartPoint, selectedEntryCenterSqFormalJacobianChartFamilyCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.lossUnit_sourceChartPoint_eq
        (chartEquiv c) u residual

/-- At an all-pivot family source point, the formal Jacobian/prior value is the
selected pivot-first formal determinant. -/
theorem jacobianPrior_sourceChartPoint_eq_det
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).jacobianPrior c
        (sourceChartPoint hcenter chartEquiv c u residual) =
      (selectedEntryPivotFirstJacobian
        (κ := {i // i ∈ center.erase (chartEquiv c).1}) u
        (fun p ↦ residual p.1)).det := by
  simpa [sourceChartPoint, selectedEntryCenterSqFormalJacobianChartFamilyCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.jacobianPrior_sourceChartPoint_eq_det
        (chartEquiv c) u residual

/-- Source-point presentation of the loss monomial identity in chart `c` of the
all-pivot selected-entry family. -/
theorem loss_monomial_sourceChartPoint
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card)
    (u : K) (residual : ι → K) :
    selectedEntryCenterSq center
        (selectedEntryChartMap (chartEquiv c).1 u residual) =
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv).lossUnit c
          (sourceChartPoint hcenter chartEquiv c u residual) *
        ∏ j : Fin (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
            (K := K) hcenter chartEquiv).numCoords,
          (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
            (K := K) hcenter chartEquiv).coord c
            (sourceChartPoint hcenter chartEquiv c u residual) j ^
            (2 *
              (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
                (K := K) hcenter chartEquiv).lossExp c j) := by
  rw [← loss_sourceChartPoint_eq_centerSq hcenter chartEquiv c u residual]
  exact
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).loss_monomial c
        (sourceChartPoint hcenter chartEquiv c u residual)

/-- Source-point presentation of the formal Jacobian/prior monomial identity
in chart `c` of the all-pivot selected-entry family. -/
theorem jacobianPrior_monomial_sourceChartPoint
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card)
    (u : K) (residual : ι → K) :
    (selectedEntryPivotFirstJacobian
        (κ := {i // i ∈ center.erase (chartEquiv c).1}) u
        (fun p ↦ residual p.1)).det =
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv).jacobianPriorUnit c
          (sourceChartPoint hcenter chartEquiv c u residual) *
        ∏ j : Fin (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
            (K := K) hcenter chartEquiv).numCoords,
          (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
            (K := K) hcenter chartEquiv).coord c
            (sourceChartPoint hcenter chartEquiv c u residual) j ^
            (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
              (K := K) hcenter chartEquiv).jacobianPriorExp c j := by
  rw [← jacobianPrior_sourceChartPoint_eq_det hcenter chartEquiv c u residual]
  exact
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).jacobianPrior_monomial c
        (sourceChartPoint hcenter chartEquiv c u residual)

end selectedEntryCenterSqFormalJacobianChartFamilyCertificate

/-- Canonical noncomputable chart enumeration for a finite center subtype.

This is only an indexing choice for finite chart-family certificates. -/
private noncomputable def finsetSubtypeChartEquiv
    {ι : Type*} [DecidableEq ι] (center : Finset ι) :
    Fin center.card ≃ center := by
  classical
  simpa [Fintype.card_coe] using (Fintype.equivFin center).symm

private theorem selectedEntryFamily_exponentMinimum_eq_centerCard_div_two
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData.exponentMinimum =
      (center.card : ℚ) / 2 := by
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  exact exponentData_exponentMinimum_eq_centerCard_div_two (K := K)
    hcenter chartEquiv

private theorem selectedEntryFamily_countInChartAtRatio_centerCard_div_two_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData.countInChartAtRatio
        ((center.card : ℚ) / 2) c = 1 := by
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  exact exponentData_countInChartAtRatio_centerCard_div_two_eq_one (K := K)
    hcenter chartEquiv c

private theorem selectedEntryFamily_minCountInChart_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (c : Fin center.card) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData.minCountInChart c = 1 := by
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  exact exponentData_minCountInChart_eq_one (K := K) hcenter chartEquiv c

private theorem selectedEntryFamily_exponentOrder_eq_one
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).exponentData.exponentOrder = 1 := by
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  exact exponentData_exponentOrder_eq_one (K := K) hcenter chartEquiv

/-- Case 2 all-pivot finite selected-entry chart-family certificate for the
residual-block center.

The charts range over every selected residual-block entry.  This is finite
certificate bookkeeping only: it does not prove source production for
non-displayed pivots, chart coverage, transition regularity, analytic Jacobian
control, normal crossings, pole order, or RLCT extraction. -/
noncomputable def case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AoyagiNormalCrossingChartCertificate
      ({p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J} → K) K :=
  selectedEntryCenterSqFormalJacobianChartFamilyCertificate
    (ι := ℕ × ℕ)
    (K := K)
    (center := case2ResidualBlockPivotEntries n S J)
    (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
    (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))

namespace case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate

/-- In any Case 2 residual-block pivot chart, the unique active coordinate has
finite ratio equal to half the residual-block selected-coordinate count. -/
theorem exponentData_ratioAt_chart_zero_eq_selectedCoordinateCount_div_two
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).exponentData.numCharts) :
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.ratioAt (c, (0 : Fin 1)) =
      (((prefixMinNat n S - J) * (n (S + 1) - J) : ℕ) : ℚ) / 2 := by
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2ResidualBlockPivotEntries_card] using
    selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_ratioAt_chart_zero
      (K := K)
      (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c

/-- In any Case 2 residual-block pivot chart, the formal Jacobian/prior
exponent equals the displayed-pivot erased-center count.  This uses only the
fact that erasing any member of the same finite center leaves the same
cardinality. -/
theorem jacobianPriorExp_chart_zero_eq_displayedFormalPivotExp
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).exponentData.numCharts) :
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).jacobianPriorExp c (0 : Fin 1) =
      ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1)).card := by
  change
    ((case2ResidualBlockPivotEntries n S J).erase
      ((finsetSubtypeChartEquiv
        (case2ResidualBlockPivotEntries n S J)) c).1).card =
    ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1)).card
  rw [Finset.card_erase_of_mem
      ((finsetSubtypeChartEquiv
        (case2ResidualBlockPivotEntries n S J)) c).2,
    Finset.card_erase_of_mem
      (case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont)]

/-- The finite exponent minimum of the Case 2 residual-block all-pivot
certificate is half the residual-block selected-coordinate count. -/
theorem exponentData_exponentMinimum_eq_selectedCoordinateCount_div_two
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.exponentMinimum =
      (((prefixMinNat n S - J) * (n (S + 1) - J) : ℕ) : ℚ) / 2 := by
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2ResidualBlockPivotEntries_card] using
    selectedEntryFamily_exponentMinimum_eq_centerCard_div_two
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))

/-- In every Case 2 residual-block pivot chart, the count at the local
selected-coordinate ratio is `1`. -/
theorem exponentData_countInChartAtRatio_selectedCoordinateCount_div_two_eq_one
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).exponentData.numCharts) :
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.countInChartAtRatio
        ((((prefixMinNat n S - J) * (n (S + 1) - J) : ℕ) : ℚ) / 2) c = 1 := by
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2ResidualBlockPivotEntries_card] using
    selectedEntryFamily_countInChartAtRatio_centerCard_div_two_eq_one
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c

/-- In every Case 2 residual-block pivot chart, the chartwise
minimum-coordinate count is `1`. -/
theorem exponentData_minCountInChart_eq_one
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).exponentData.numCharts) :
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.minCountInChart c = 1 := by
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
    selectedEntryFamily_minCountInChart_eq_one
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c

/-- The Case 2 residual-block all-pivot finite certificate has finite
exponent order `1`. -/
theorem exponentData_exponentOrder_eq_one
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.exponentOrder = 1 := by
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
    selectedEntryFamily_exponentOrder_eq_one
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))

/-- Any chart of the Case 2 residual-block all-pivot finite certificate has
the same finite selected-entry exponent pattern as the displayed Case 2
continuing bridge.

This is only an exponent-array adapter.  It does not identify a non-displayed
pivot chart with Aoyagi's displayed source chart, and it does not prove source
production, chart coverage, regularity, or a global A0 lower bound. -/
theorem localExponentCoordinateBridge_anyChart
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
        L n S J t numerator leastValue pre u residual hS hcont C)
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).exponentData.numCharts) :
    Case2DisplayedContinuingExponentCoordinateBridge cert
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData
      (c, (0 : Fin 1)) where
  lossExp_eq_one := rfl
  jacobianPriorExp_eq_formalPivotExp :=
    jacobianPriorExp_chart_zero_eq_displayedFormalPivotExp
      (K := K) n hS hcont c

/-- Local finite contribution summary for an arbitrary chart of the Case 2
residual-block all-pivot certificate.

This bundles exponent-array compatibility with the chart's finite ratio,
minimum, chart-count, minimum-count, and order facts. -/
theorem localChartFamilyCertificateContribution_summary
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
        L n S J t numerator leastValue pre u residual hS hcont C)
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).exponentData.numCharts) :
    Case2DisplayedContinuingExponentCoordinateBridge cert
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).exponentData
      (c, (0 : Fin 1)) ∧
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.ratioAt (c, (0 : Fin 1)) =
      (((prefixMinNat n S - J) * (n (S + 1) - J) : ℕ) : ℚ) / 2 ∧
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.exponentMinimum =
      (((prefixMinNat n S - J) * (n (S + 1) - J) : ℕ) : ℚ) / 2 ∧
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.countInChartAtRatio
        ((((prefixMinNat n S - J) * (n (S + 1) - J) : ℕ) : ℚ) / 2) c = 1 ∧
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.minCountInChart c = 1 ∧
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.exponentOrder = 1 := by
  let B := localExponentCoordinateBridge_anyChart cert c
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · exact exponentData_ratioAt_chart_zero_eq_selectedCoordinateCount_div_two
      (K := K) n hS hcont c
  · exact exponentData_exponentMinimum_eq_selectedCoordinateCount_div_two
      (K := K) n hS hcont
  · exact exponentData_countInChartAtRatio_selectedCoordinateCount_div_two_eq_one
      (K := K) n hS hcont c
  · exact exponentData_minCountInChart_eq_one (K := K) n hS hcont c
  · exact exponentData_exponentOrder_eq_one (K := K) n hS hcont

end case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate

/-- Case 1 all-pivot finite selected-entry chart-family certificate for the
center consisting of the old exceptional generator and the row strip.

The charts range over every finite Case 1 center generator.  This is finite
certificate bookkeeping only: it does not prove source production for
arbitrary pivots, chart coverage, transition regularity, analytic Jacobian
control, normal crossings, pole order, or RLCT extraction. -/
noncomputable def case1CenterSqFormalJacobianChartFamilyCertificate
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AoyagiNormalCrossingChartCertificate
      ({g : Case1CenterGenerator // g ∈ case1CenterGenerators n S J J1} → K) K :=
  selectedEntryCenterSqFormalJacobianChartFamilyCertificate
    (ι := Case1CenterGenerator)
    (K := K)
    (center := case1CenterGenerators n S J J1)
    (case1CenterGenerators_nonempty n S J J1)
    (finsetSubtypeChartEquiv (case1CenterGenerators n S J J1))

namespace case1CenterSqFormalJacobianChartFamilyCertificate

/-- In any Case 1 center-generator pivot chart, the unique active coordinate
has finite ratio equal to half the Case 1 selected-coordinate count. -/
theorem exponentData_ratioAt_chart_zero_eq_nonpivotCount_add_one_div_two
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case1CenterSqFormalJacobianChartFamilyCertificate
        (K := K) n S J J1).exponentData.numCharts) :
    (case1CenterSqFormalJacobianChartFamilyCertificate
      (K := K) n S J J1).exponentData.ratioAt (c, (0 : Fin 1)) =
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 := by
  simpa [case1CenterSqFormalJacobianChartFamilyCertificate,
    case1CenterGenerators_card, case1StripEntries_card] using
    selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_ratioAt_chart_zero
      (K := K)
      (case1CenterGenerators_nonempty n S J J1)
      (finsetSubtypeChartEquiv (case1CenterGenerators n S J J1)) c

/-- In any Case 1 center-generator pivot chart, the formal Jacobian/prior
exponent equals the non-pivot Case 1 center count. -/
theorem jacobianPriorExp_chart_zero_eq_nonpivotCount
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case1CenterSqFormalJacobianChartFamilyCertificate
        (K := K) n S J J1).exponentData.numCharts) :
    (case1CenterSqFormalJacobianChartFamilyCertificate
      (K := K) n S J J1).jacobianPriorExp c (0 : Fin 1) =
      J1 * (n (S + 1) - J) := by
  change
    ((case1CenterGenerators n S J J1).erase
      ((finsetSubtypeChartEquiv
        (case1CenterGenerators n S J J1)) c).1).card =
    J1 * (n (S + 1) - J)
  exact case1CenterGenerators_erase_card_of_mem
    ((finsetSubtypeChartEquiv (case1CenterGenerators n S J J1)) c).2

/-- The finite exponent minimum of the Case 1 all-pivot certificate is half
the Case 1 selected-coordinate count. -/
theorem exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1CenterSqFormalJacobianChartFamilyCertificate
      (K := K) n S J J1).exponentData.exponentMinimum =
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 := by
  simpa [case1CenterSqFormalJacobianChartFamilyCertificate,
    case1CenterGenerators_card, case1StripEntries_card] using
    selectedEntryFamily_exponentMinimum_eq_centerCard_div_two
        (K := K)
        (case1CenterGenerators_nonempty n S J J1)
        (finsetSubtypeChartEquiv (case1CenterGenerators n S J J1))

/-- In every Case 1 center-generator pivot chart, the count at the local
Case 1 selected-coordinate ratio is `1`. -/
theorem exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case1CenterSqFormalJacobianChartFamilyCertificate
        (K := K) n S J J1).exponentData.numCharts) :
    (case1CenterSqFormalJacobianChartFamilyCertificate
      (K := K) n S J J1).exponentData.countInChartAtRatio
        (((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2) c = 1 := by
  simpa [case1CenterSqFormalJacobianChartFamilyCertificate,
    case1CenterGenerators_card, case1StripEntries_card] using
    selectedEntryFamily_countInChartAtRatio_centerCard_div_two_eq_one
        (K := K)
        (case1CenterGenerators_nonempty n S J J1)
        (finsetSubtypeChartEquiv (case1CenterGenerators n S J J1)) c

/-- In every Case 1 center-generator pivot chart, the chartwise
minimum-coordinate count is `1`. -/
theorem exponentData_minCountInChart_eq_one
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case1CenterSqFormalJacobianChartFamilyCertificate
        (K := K) n S J J1).exponentData.numCharts) :
    (case1CenterSqFormalJacobianChartFamilyCertificate
      (K := K) n S J J1).exponentData.minCountInChart c = 1 := by
  simpa [case1CenterSqFormalJacobianChartFamilyCertificate] using
    selectedEntryFamily_minCountInChart_eq_one
        (K := K)
        (case1CenterGenerators_nonempty n S J J1)
        (finsetSubtypeChartEquiv (case1CenterGenerators n S J J1)) c

/-- The Case 1 all-pivot finite certificate has finite exponent order `1`. -/
theorem exponentData_exponentOrder_eq_one
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1CenterSqFormalJacobianChartFamilyCertificate
      (K := K) n S J J1).exponentData.exponentOrder = 1 := by
  simpa [case1CenterSqFormalJacobianChartFamilyCertificate] using
    selectedEntryFamily_exponentOrder_eq_one
        (K := K)
        (case1CenterGenerators_nonempty n S J J1)
        (finsetSubtypeChartEquiv (case1CenterGenerators n S J J1))

end case1CenterSqFormalJacobianChartFamilyCertificate

/-- Case 1 specialization of the selected-entry finite microcertificate at
the old exceptional generator.

The certificate covers only the finite Case 1 center square-sum and formal
selected-entry determinant for this chart.  The hidden source label behind the
old generator, chart production, and analytic Jacobian control remain outside
this local finite certificate. -/
def case1SelectedOldCenterSqFormalJacobianChartCertificate
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AoyagiNormalCrossingChartCertificate
      ({g : Case1CenterGenerator // g ∈ case1CenterGenerators n S J J1} → K) K :=
  selectedEntryCenterSqFormalJacobianChartCertificate
    (ι := Case1CenterGenerator)
    (K := K)
    (center := case1CenterGenerators n S J J1)
    ⟨(Sum.inl () : Case1CenterGenerator), by simp [case1CenterGenerators]⟩

namespace case1SelectedOldCenterSqFormalJacobianChartCertificate

/-- The point of the Case 1 selected-old microcertificate corresponding to
finite selected-entry source coordinates. -/
def sourceChartPoint
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).ChartPoint (0 : Fin 1) :=
  selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint
    (K := K)
    (pivot := ⟨(Sum.inl () : Case1CenterGenerator),
      case1_selectedOld_mem_center n S J J1⟩)
    u residual

/-- The selected-old microcertificate chart map agrees with the finite
selected-old selected-entry source chart map at `sourceChartPoint`. -/
theorem chartMap_sourceChartPoint_eq
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).chartMap (0 : Fin 1)
        (sourceChartPoint n S J J1 u residual) =
      fun g : {g // g ∈ case1CenterGenerators n S J J1} ↦
        selectedEntryChartMap (Sum.inl () : Case1CenterGenerator)
          u residual g.1 := by
  simpa [sourceChartPoint, case1SelectedOldCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.chartMap_sourceChartPoint_eq
        (K := K)
        (pivot := ⟨(Sum.inl () : Case1CenterGenerator),
          case1_selectedOld_mem_center n S J J1⟩)
        u residual

/-- At the selected-old source chart point, the microcertificate loss is the
finite Case 1 center square-sum. -/
theorem loss_sourceChartPoint_eq_centerSq
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).loss
        ((case1SelectedOldCenterSqFormalJacobianChartCertificate
          (K := K) n S J J1).chartMap (0 : Fin 1)
            (sourceChartPoint n S J J1 u residual)) =
      selectedEntryCenterSq (case1CenterGenerators n S J J1)
        (selectedEntryChartMap (Sum.inl () : Case1CenterGenerator)
          u residual) := by
  simpa [sourceChartPoint, case1SelectedOldCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.loss_sourceChartPoint_eq_centerSq
        (K := K)
        (pivot := ⟨(Sum.inl () : Case1CenterGenerator),
          case1_selectedOld_mem_center n S J J1⟩)
        u residual

/-- At the selected-old source chart point, the microcertificate loss unit is
the normalized finite Case 1 center-square factor. -/
theorem lossUnit_sourceChartPoint_eq
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).lossUnit (0 : Fin 1)
        (sourceChartPoint n S J J1 u residual) =
      selectedEntryCenterSqUnitFactor
        ((case1CenterGenerators n S J J1).erase
          (Sum.inl () : Case1CenterGenerator)) residual := by
  simpa [sourceChartPoint, case1SelectedOldCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.lossUnit_sourceChartPoint_eq
        (K := K)
        (pivot := ⟨(Sum.inl () : Case1CenterGenerator),
          case1_selectedOld_mem_center n S J J1⟩)
        u residual

/-- At the selected-old source chart point, the microcertificate
Jacobian/prior value is the formal pivot-first determinant. -/
theorem jacobianPrior_sourceChartPoint_eq_det
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).jacobianPrior (0 : Fin 1)
        (sourceChartPoint n S J J1 u residual) =
      (selectedEntryPivotFirstJacobian
        (κ :=
          ((case1CenterGenerators n S J J1).erase
            (Sum.inl () : Case1CenterGenerator) : Type))
        u (fun g ↦ residual g.1)).det := by
  simpa [sourceChartPoint, case1SelectedOldCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.jacobianPrior_sourceChartPoint_eq_det
        (K := K)
        (pivot := ⟨(Sum.inl () : Case1CenterGenerator),
          case1_selectedOld_mem_center n S J J1⟩)
        u residual

/-- Source-chart presentation of the selected-old loss monomial identity. -/
theorem loss_monomial_sourceChartPoint
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    selectedEntryCenterSq (case1CenterGenerators n S J J1)
        (selectedEntryChartMap (Sum.inl () : Case1CenterGenerator)
          u residual) =
      selectedEntryCenterSqUnitFactor
          ((case1CenterGenerators n S J J1).erase
            (Sum.inl () : Case1CenterGenerator)) residual *
        ∏ j : Fin (case1SelectedOldCenterSqFormalJacobianChartCertificate
            (K := K) n S J J1).numCoords,
          (case1SelectedOldCenterSqFormalJacobianChartCertificate
            (K := K) n S J J1).coord (0 : Fin 1)
            (sourceChartPoint n S J J1 u residual) j ^
            (2 *
              (case1SelectedOldCenterSqFormalJacobianChartCertificate
                (K := K) n S J J1).lossExp (0 : Fin 1) j) := by
  simpa [sourceChartPoint, case1SelectedOldCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.loss_monomial_sourceChartPoint
        (K := K)
        (pivot := ⟨(Sum.inl () : Case1CenterGenerator),
          case1_selectedOld_mem_center n S J J1⟩)
        u residual

/-- Source-chart presentation of the selected-old formal Jacobian/prior
monomial identity. -/
theorem jacobianPrior_monomial_sourceChartPoint
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (selectedEntryPivotFirstJacobian
        (κ :=
          ((case1CenterGenerators n S J J1).erase
            (Sum.inl () : Case1CenterGenerator) : Type))
        u (fun g ↦ residual g.1)).det =
      (case1SelectedOldCenterSqFormalJacobianChartCertificate
          (K := K) n S J J1).jacobianPriorUnit (0 : Fin 1)
          (sourceChartPoint n S J J1 u residual) *
        ∏ j : Fin (case1SelectedOldCenterSqFormalJacobianChartCertificate
            (K := K) n S J J1).numCoords,
          (case1SelectedOldCenterSqFormalJacobianChartCertificate
            (K := K) n S J J1).coord (0 : Fin 1)
            (sourceChartPoint n S J J1 u residual) j ^
            (case1SelectedOldCenterSqFormalJacobianChartCertificate
              (K := K) n S J J1).jacobianPriorExp (0 : Fin 1) j := by
  simpa [sourceChartPoint, case1SelectedOldCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.jacobianPrior_monomial_sourceChartPoint
        (K := K)
        (pivot := ⟨(Sum.inl () : Case1CenterGenerator),
          case1_selectedOld_mem_center n S J J1⟩)
        u residual

/-- The unique coordinate in the Case 1 selected-old finite microcertificate
has loss exponent `1`. -/
@[simp] theorem lossExp_zero_zero
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).lossExp (0 : Fin 1) (0 : Fin 1) = 1 :=
  rfl

/-- The unique coordinate in the Case 1 selected-old finite microcertificate
has formal Jacobian/prior exponent equal to the row-strip cardinality. -/
@[simp] theorem jacobianPriorExp_zero_zero
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).jacobianPriorExp (0 : Fin 1) (0 : Fin 1) =
      J1 * (n (S + 1) - J) := by
  change
    ((case1CenterGenerators n S J J1).erase
        (Sum.inl () : Case1CenterGenerator)).card =
      J1 * (n (S + 1) - J)
  exact case1CenterGenerators_erase_selectedOld_card n S J J1

/-- The unique coordinate in the Case 1 selected-old finite microcertificate
has finite exponent ratio `(1 + J1 * (n(S+1)-J)) / 2`. -/
theorem exponentData_ratioAt_zero_zero
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).exponentData.ratioAt
        ((0 : Fin 1), (0 : Fin 1)) =
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 := by
  simpa [case1SelectedOldCenterSqFormalJacobianChartCertificate,
    case1CenterGenerators_card, case1StripEntries_card] using
    selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero
      (K := K)
      (⟨(Sum.inl () : Case1CenterGenerator), case1_selectedOld_mem_center n S J J1⟩)

/-- The finite exponent minimum of the Case 1 selected-old local
microcertificate is `(1 + J1 * (n(S+1)-J)) / 2`. -/
theorem exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).exponentData.exponentMinimum =
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 := by
  open selectedEntryCenterSqFormalJacobianChartCertificate in
  simpa [case1SelectedOldCenterSqFormalJacobianChartCertificate,
    case1CenterGenerators_card, case1StripEntries_card] using
    exponentData_exponentMinimum_eq_centerCard_div_two (K := K)
      (⟨(Sum.inl () : Case1CenterGenerator), case1_selectedOld_mem_center n S J J1⟩)

/-- In the Case 1 selected-old local microcertificate, the chart count at the
local Case 1 ratio is `1`. -/
theorem exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case1SelectedOldCenterSqFormalJacobianChartCertificate
        (K := K) n S J J1).exponentData.numCharts) :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).exponentData.countInChartAtRatio
        (((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2) c = 1 := by
  simpa [case1SelectedOldCenterSqFormalJacobianChartCertificate,
    case1CenterGenerators_card, case1StripEntries_card] using
    selectedEntryCenterSqFormalJacobianChartCertificate.countAtLocalRatio_eq_one
      (K := K)
      (pivot := ⟨(Sum.inl () : Case1CenterGenerator),
        case1_selectedOld_mem_center n S J J1⟩)
      c

/-- In the Case 1 selected-old local microcertificate, the chartwise
minimum-coordinate count is `1`. -/
theorem exponentData_minCountInChart_eq_one
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case1SelectedOldCenterSqFormalJacobianChartCertificate
        (K := K) n S J J1).exponentData.numCharts) :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).exponentData.minCountInChart c = 1 := by
  simpa [case1SelectedOldCenterSqFormalJacobianChartCertificate] using
    selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one
      (K := K)
      (pivot := ⟨(Sum.inl () : Case1CenterGenerator),
        case1_selectedOld_mem_center n S J J1⟩)
      c

/-- The Case 1 selected-old local one-coordinate microcertificate has finite
exponent order `1`. -/
theorem exponentData_exponentOrder_eq_one
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1SelectedOldCenterSqFormalJacobianChartCertificate
      (K := K) n S J J1).exponentData.exponentOrder = 1 := by
  simpa [case1SelectedOldCenterSqFormalJacobianChartCertificate] using
    selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one
      (K := K)
      (⟨(Sum.inl () : Case1CenterGenerator), case1_selectedOld_mem_center n S J J1⟩)

/-- Formal pivot-first determinant for the Case 1 selected-old chart. -/
theorem pivotFirstJacobian_det
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {R : Type*} [CommRing R]
    (u : R)
    (residual :
      ((case1CenterGenerators n S J J1).erase
        (Sum.inl () : Case1CenterGenerator) : Type) → R) :
    (selectedEntryPivotFirstJacobian
        (κ :=
          ((case1CenterGenerators n S J J1).erase
            (Sum.inl () : Case1CenterGenerator) : Type))
        u residual).det =
      u ^ (J1 * (n (S + 1) - J)) := by
  have hcard :
      Fintype.card
          ((case1CenterGenerators n S J J1).erase
            (Sum.inl () : Case1CenterGenerator) : Type) =
        J1 * (n (S + 1) - J) := by
    simpa [Fintype.card_coe] using
      case1CenterGenerators_erase_selectedOld_card n S J J1
  rw [selectedEntryPivotFirstJacobian_det, hcard]

end case1SelectedOldCenterSqFormalJacobianChartCertificate

/-- Case 1 specialization of the selected-entry finite microcertificate at
Aoyagi's displayed row-strip pivot `d_(J+1,J+1)`.

The certificate covers only the finite Case 1 center square-sum and formal
selected-entry determinant for this chart.  It is not chart coverage,
transition regularity, or an analytic Jacobian/volume-form theorem. -/
def case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AoyagiNormalCrossingChartCertificate
      ({g : Case1CenterGenerator // g ∈ case1CenterGenerators n S J J1} → K) K :=
  selectedEntryCenterSqFormalJacobianChartCertificate
    (ι := Case1CenterGenerator)
    (K := K)
    (center := case1CenterGenerators n S J J1)
    ⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
      case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩

namespace case1DisplayedRowStripCenterSqFormalJacobianChartCertificate

/-- The point of the displayed Case 1 row-strip microcertificate
corresponding to finite selected-entry source coordinates. -/
def sourceChartPoint
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).ChartPoint (0 : Fin 1) :=
  selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint
    (K := K)
    (pivot := ⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
      case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)
    u residual

/-- The displayed row-strip microcertificate chart map agrees with the finite
displayed selected-entry source chart map at `sourceChartPoint`. -/
theorem chartMap_sourceChartPoint_eq
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).chartMap (0 : Fin 1)
        (sourceChartPoint n S hJ1 hcol u residual) =
      fun g : {g // g ∈ case1CenterGenerators n S J J1} ↦
        selectedEntryChartMap
          (Sum.inr (J + 1, J + 1) : Case1CenterGenerator)
          u residual g.1 := by
  simpa [sourceChartPoint, case1DisplayedRowStripCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.chartMap_sourceChartPoint_eq
        (K := K)
        (pivot := ⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
          case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)
        u residual

/-- At the displayed row-strip source chart point, the microcertificate loss
is the finite Case 1 center square-sum. -/
theorem loss_sourceChartPoint_eq_centerSq
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).loss
        ((case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
          (K := K) n S hJ1 hcol).chartMap (0 : Fin 1)
            (sourceChartPoint n S hJ1 hcol u residual)) =
      selectedEntryCenterSq (case1CenterGenerators n S J J1)
        (selectedEntryChartMap
          (Sum.inr (J + 1, J + 1) : Case1CenterGenerator)
          u residual) := by
  simpa [sourceChartPoint, case1DisplayedRowStripCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.loss_sourceChartPoint_eq_centerSq
        (K := K)
        (pivot := ⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
          case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)
        u residual

/-- At the displayed row-strip source chart point, the microcertificate loss
unit is the normalized finite Case 1 center-square factor. -/
theorem lossUnit_sourceChartPoint_eq
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).lossUnit (0 : Fin 1)
        (sourceChartPoint n S hJ1 hcol u residual) =
      selectedEntryCenterSqUnitFactor
        ((case1CenterGenerators n S J J1).erase
          (Sum.inr (J + 1, J + 1) : Case1CenterGenerator)) residual := by
  simpa [sourceChartPoint, case1DisplayedRowStripCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.lossUnit_sourceChartPoint_eq
        (K := K)
        (pivot := ⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
          case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)
        u residual

/-- At the displayed row-strip source chart point, the microcertificate
Jacobian/prior value is the formal pivot-first determinant. -/
theorem jacobianPrior_sourceChartPoint_eq_det
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).jacobianPrior (0 : Fin 1)
        (sourceChartPoint n S hJ1 hcol u residual) =
      (selectedEntryPivotFirstJacobian
        (κ :=
          ((case1CenterGenerators n S J J1).erase
            (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) : Type))
        u (fun g ↦ residual g.1)).det := by
  simpa [sourceChartPoint, case1DisplayedRowStripCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.jacobianPrior_sourceChartPoint_eq_det
        (K := K)
        (pivot := ⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
          case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)
        u residual

/-- Source-chart presentation of the displayed row-strip loss monomial
identity. -/
theorem loss_monomial_sourceChartPoint
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    selectedEntryCenterSq (case1CenterGenerators n S J J1)
        (selectedEntryChartMap
          (Sum.inr (J + 1, J + 1) : Case1CenterGenerator)
          u residual) =
      selectedEntryCenterSqUnitFactor
          ((case1CenterGenerators n S J J1).erase
            (Sum.inr (J + 1, J + 1) : Case1CenterGenerator)) residual *
        ∏ j : Fin (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
            (K := K) n S hJ1 hcol).numCoords,
          (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
            (K := K) n S hJ1 hcol).coord (0 : Fin 1)
            (sourceChartPoint n S hJ1 hcol u residual) j ^
            (2 *
              (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
                (K := K) n S hJ1 hcol).lossExp (0 : Fin 1) j) := by
  simpa [sourceChartPoint, case1DisplayedRowStripCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.loss_monomial_sourceChartPoint
        (K := K)
        (pivot := ⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
          case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)
        u residual

/-- Source-chart presentation of the displayed row-strip formal
Jacobian/prior monomial identity. -/
theorem jacobianPrior_monomial_sourceChartPoint
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : Case1CenterGenerator → K) :
    (selectedEntryPivotFirstJacobian
        (κ :=
          ((case1CenterGenerators n S J J1).erase
            (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) : Type))
        u (fun g ↦ residual g.1)).det =
      (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
          (K := K) n S hJ1 hcol).jacobianPriorUnit (0 : Fin 1)
          (sourceChartPoint n S hJ1 hcol u residual) *
        ∏ j : Fin (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
            (K := K) n S hJ1 hcol).numCoords,
          (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
            (K := K) n S hJ1 hcol).coord (0 : Fin 1)
            (sourceChartPoint n S hJ1 hcol u residual) j ^
            (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
              (K := K) n S hJ1 hcol).jacobianPriorExp (0 : Fin 1) j := by
  simpa [sourceChartPoint, case1DisplayedRowStripCenterSqFormalJacobianChartCertificate]
    using
      selectedEntryCenterSqFormalJacobianChartCertificate.jacobianPrior_monomial_sourceChartPoint
        (K := K)
        (pivot := ⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
          case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)
        u residual

/-- The unique coordinate in the displayed Case 1 row-strip finite
microcertificate has loss exponent `1`. -/
@[simp] theorem lossExp_zero_zero
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).lossExp (0 : Fin 1) (0 : Fin 1) = 1 :=
  rfl

/-- The unique coordinate in the Case 1 displayed row-strip finite
microcertificate has formal Jacobian/prior exponent equal to the row-strip
cardinality. -/
@[simp] theorem jacobianPriorExp_zero_zero
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).jacobianPriorExp (0 : Fin 1) (0 : Fin 1) =
      J1 * (n (S + 1) - J) := by
  change
    ((case1CenterGenerators n S J J1).erase
        (Sum.inr (J + 1, J + 1) : Case1CenterGenerator)).card =
      J1 * (n (S + 1) - J)
  exact case1CenterGenerators_erase_displayedPivot_card_of_bounds n S hJ1 hcol

/-- The unique coordinate in the displayed Case 1 row-strip finite
microcertificate has finite exponent ratio
`(1 + J1 * (n(S+1)-J)) / 2`. -/
theorem exponentData_ratioAt_zero_zero
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).exponentData.ratioAt
        ((0 : Fin 1), (0 : Fin 1)) =
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 := by
  simpa [case1DisplayedRowStripCenterSqFormalJacobianChartCertificate,
    case1CenterGenerators_card, case1StripEntries_card] using
    selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero
      (K := K)
      (⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
        case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)

/-- The finite exponent minimum of the displayed Case 1 row-strip local
microcertificate is `(1 + J1 * (n(S+1)-J)) / 2`. -/
theorem exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).exponentData.exponentMinimum =
      ((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2 := by
  open selectedEntryCenterSqFormalJacobianChartCertificate in
  simpa [case1DisplayedRowStripCenterSqFormalJacobianChartCertificate,
    case1CenterGenerators_card, case1StripEntries_card] using
    exponentData_exponentMinimum_eq_centerCard_div_two (K := K)
      (⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
        case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)

/-- In the displayed Case 1 row-strip local microcertificate, the chart count
at the local Case 1 ratio is `1`. -/
theorem exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
        (K := K) n S hJ1 hcol).exponentData.numCharts) :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).exponentData.countInChartAtRatio
        (((1 + J1 * (n (S + 1) - J) : ℕ) : ℚ) / 2) c = 1 := by
  simpa [case1DisplayedRowStripCenterSqFormalJacobianChartCertificate,
    case1CenterGenerators_card, case1StripEntries_card] using
    selectedEntryCenterSqFormalJacobianChartCertificate.countAtLocalRatio_eq_one
      (K := K)
      (pivot := ⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
        case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)
      c

/-- In the displayed Case 1 row-strip local microcertificate, the chartwise
minimum-coordinate count is `1`. -/
theorem exponentData_minCountInChart_eq_one
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
        (K := K) n S hJ1 hcol).exponentData.numCharts) :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).exponentData.minCountInChart c = 1 := by
  simpa [case1DisplayedRowStripCenterSqFormalJacobianChartCertificate] using
    selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one
      (K := K)
      (pivot := ⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
        case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)
      c

/-- The displayed Case 1 row-strip local one-coordinate microcertificate has
finite exponent order `1`. -/
theorem exponentData_exponentOrder_eq_one
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
      (K := K) n S hJ1 hcol).exponentData.exponentOrder = 1 := by
  simpa [case1DisplayedRowStripCenterSqFormalJacobianChartCertificate] using
    selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one
      (K := K)
      (⟨(Sum.inr (J + 1, J + 1) : Case1CenterGenerator),
        case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol⟩)

/-- Formal pivot-first determinant for the displayed Case 1 row-strip chart. -/
theorem pivotFirstJacobian_det
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {R : Type*} [CommRing R]
    (u : R)
    (residual :
      ((case1CenterGenerators n S J J1).erase
        (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) : Type) → R) :
    (selectedEntryPivotFirstJacobian
        (κ :=
          ((case1CenterGenerators n S J J1).erase
            (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) : Type))
        u residual).det =
      u ^ (J1 * (n (S + 1) - J)) := by
  have hcard :
      Fintype.card
          ((case1CenterGenerators n S J J1).erase
            (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) : Type) =
        J1 * (n (S + 1) - J) := by
    simpa [Fintype.card_coe] using
      case1CenterGenerators_erase_displayedPivot_card_of_bounds n S hJ1 hcol
  rw [selectedEntryPivotFirstJacobian_det, hcard]

end case1DisplayedRowStripCenterSqFormalJacobianChartCertificate

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

/-- The point of the local selected-entry microcertificate corresponding to
the displayed continuing Case 2 source-chart coordinates. -/
def sourceChartPoint
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : ℕ × ℕ → K) :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).ChartPoint (0 : Fin 1) :=
  (u, fun p ↦ residual p.1)

/-- The local selected-entry microcertificate chart map agrees with the
displayed continuing Case 2 source chart map at `sourceChartPoint`. -/
theorem chartMap_sourceChartPoint_eq
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : ℕ × ℕ → K) :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).chartMap (0 : Fin 1)
        (sourceChartPoint n hS hcont u residual) =
      fun p : {p // p ∈ case2ResidualBlockPivotEntries n S J} ↦
        case2DisplayedSourceChartMap n hS hcont u residual p.1 := by
  funext p
  by_cases hp : p.1 = (J + 1, J + 1)
  · simp [sourceChartPoint, case2DisplayedCenterSqFormalJacobianChartCertificate,
      selectedEntryCenterSqFormalJacobianChartCertificate, case2DisplayedSourceChartMap,
      selectedEntryChartMap, hp]
  · have hmem :
        p.1 ∈ (case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1) := by
      simp [Finset.mem_erase, hp, p.2]
    simp [sourceChartPoint, case2DisplayedCenterSqFormalJacobianChartCertificate,
      selectedEntryCenterSqFormalJacobianChartCertificate, case2DisplayedSourceChartMap,
      selectedEntryChartMap, selectedEntryErasedResidual, hp, hmem]

/-- At the displayed continuing Case 2 source-chart point, the local
microcertificate loss is the finite residual-center square-sum. -/
theorem loss_sourceChartPoint_eq_centerSq
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : ℕ × ℕ → K) :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).loss
        ((case2DisplayedCenterSqFormalJacobianChartCertificate
          (K := K) n hS hcont).chartMap (0 : Fin 1)
            (sourceChartPoint n hS hcont u residual)) =
      selectedEntryCenterSq (case2ResidualBlockPivotEntries n S J)
        (case2DisplayedSourceChartMap n hS hcont u residual) := by
  rw [chartMap_sourceChartPoint_eq]
  simpa [case2DisplayedCenterSqFormalJacobianChartCertificate,
    selectedEntryCenterSqFormalJacobianChartCertificate, selectedEntryCenterSq] using
    (Finset.sum_attach (case2ResidualBlockPivotEntries n S J)
      (fun p ↦ case2DisplayedSourceChartMap n hS hcont u residual p ^ 2))

/-- At the displayed continuing Case 2 source-chart point, the local
microcertificate loss unit is the normalized finite center-square factor. -/
theorem lossUnit_sourceChartPoint_eq
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : ℕ × ℕ → K) :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).lossUnit (0 : Fin 1)
        (sourceChartPoint n hS hcont u residual) =
      selectedEntryCenterSqUnitFactor
        ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1)) residual := by
  simp only [sourceChartPoint, case2DisplayedCenterSqFormalJacobianChartCertificate,
    selectedEntryCenterSqFormalJacobianChartCertificate]
  rw [selectedEntryCenterSqUnitFactor, selectedEntryCenterSqUnitFactor]
  congr 1
  rw [selectedEntryCenterSq, selectedEntryCenterSq]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hmem :
      p ∈ (case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1) := hp
  simp [selectedEntryErasedResidual, hmem]

/-- At the displayed continuing Case 2 source-chart point, the local
microcertificate Jacobian/prior value is the formal pivot-first determinant. -/
theorem jacobianPrior_sourceChartPoint_eq_det
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : ℕ × ℕ → K) :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).jacobianPrior (0 : Fin 1)
        (sourceChartPoint n hS hcont u residual) =
      (selectedEntryPivotFirstJacobian
        (κ := ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1) : Type))
        u (fun p ↦ residual p.1)).det := by
  rw [case2DisplayedSourceChartMap_pivotFirstJacobian_det n hS hcont u residual]
  simp [sourceChartPoint, case2DisplayedCenterSqFormalJacobianChartCertificate,
    selectedEntryCenterSqFormalJacobianChartCertificate]

/-- Source-chart presentation of the local selected-entry loss monomial
identity for the displayed continuing Case 2 microcertificate. -/
theorem loss_monomial_sourceChartPoint
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : ℕ × ℕ → K) :
    selectedEntryCenterSq (case2ResidualBlockPivotEntries n S J)
        (case2DisplayedSourceChartMap n hS hcont u residual) =
      selectedEntryCenterSqUnitFactor
          ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1)) residual *
        ∏ j : Fin (case2DisplayedCenterSqFormalJacobianChartCertificate
            (K := K) n hS hcont).numCoords,
          (case2DisplayedCenterSqFormalJacobianChartCertificate
            (K := K) n hS hcont).coord (0 : Fin 1)
            (sourceChartPoint n hS hcont u residual) j ^
            (2 *
              (case2DisplayedCenterSqFormalJacobianChartCertificate
                (K := K) n hS hcont).lossExp (0 : Fin 1) j) := by
  rw [← loss_sourceChartPoint_eq_centerSq n hS hcont u residual]
  rw [← lossUnit_sourceChartPoint_eq n hS hcont u residual]
  exact
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).loss_monomial
        (0 : Fin 1) (sourceChartPoint n hS hcont u residual)

/-- Source-chart presentation of the local selected-entry formal
Jacobian/prior monomial identity for the displayed continuing Case 2
microcertificate. -/
theorem jacobianPrior_monomial_sourceChartPoint
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (u : K) (residual : ℕ × ℕ → K) :
    (selectedEntryPivotFirstJacobian
        (κ := ((case2ResidualBlockPivotEntries n S J).erase (J + 1, J + 1) : Type))
        u (fun p ↦ residual p.1)).det =
      (case2DisplayedCenterSqFormalJacobianChartCertificate
          (K := K) n hS hcont).jacobianPriorUnit (0 : Fin 1)
          (sourceChartPoint n hS hcont u residual) *
        ∏ j : Fin (case2DisplayedCenterSqFormalJacobianChartCertificate
            (K := K) n hS hcont).numCoords,
          (case2DisplayedCenterSqFormalJacobianChartCertificate
            (K := K) n hS hcont).coord (0 : Fin 1)
            (sourceChartPoint n hS hcont u residual) j ^
            (case2DisplayedCenterSqFormalJacobianChartCertificate
              (K := K) n hS hcont).jacobianPriorExp (0 : Fin 1) j := by
  rw [← jacobianPrior_sourceChartPoint_eq_det n hS hcont u residual]
  exact
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).jacobianPrior_monomial
        (0 : Fin 1) (sourceChartPoint n hS hcont u residual)

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

/-- In the displayed Case 2 local microcertificate, the chart count at half
the residual-block center cardinality is `1`. -/
theorem exponentData_countInChartAtRatio_centerCard_div_two_eq_one
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2DisplayedCenterSqFormalJacobianChartCertificate
        (K := K) n hS hcont).exponentData.numCharts) :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData.countInChartAtRatio
        (((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2) c = 1 := by
  simpa [case2DisplayedCenterSqFormalJacobianChartCertificate] using
    selectedEntryCenterSqFormalJacobianChartCertificate.countAtLocalRatio_eq_one
      (K := K)
      (pivot := ⟨(J + 1, J + 1),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont⟩)
      c

/-- In the displayed Case 2 local microcertificate, the chartwise
minimum-coordinate count is `1`. -/
theorem exponentData_minCountInChart_eq_one
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2DisplayedCenterSqFormalJacobianChartCertificate
        (K := K) n hS hcont).exponentData.numCharts) :
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData.minCountInChart c = 1 := by
  simpa [case2DisplayedCenterSqFormalJacobianChartCertificate] using
    selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one
      (K := K)
      (pivot := ⟨(J + 1, J + 1),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont⟩)
      c

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
    Case2DisplayedContinuingExponentCoordinateBridge cert
      (case2DisplayedCenterSqFormalJacobianChartCertificate
        (K := K) n hS hcont).exponentData
      ((0 : Fin 1), (0 : Fin 1)) where
  lossExp_eq_one := rfl
  jacobianPriorExp_eq_formalPivotExp := rfl

/-- Local finite contribution of the displayed continuing Case 2
selected-entry chart certificate.

This bundles the source-coordinate bridge with the local one-chart finite
ratio, minimum, chart-count, minimum-count, and order facts for this
microcertificate's own exponent data.  It does not construct the global A0
chart family and does not prove a global lower bound, pole order, or RLCT. -/
theorem localChartCertificateContribution_summary
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
    Case2DisplayedContinuingExponentCoordinateBridge cert
      (case2DisplayedCenterSqFormalJacobianChartCertificate
        (K := K) n hS hcont).exponentData
      ((0 : Fin 1), (0 : Fin 1)) ∧
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData.ratioAt
        ((0 : Fin 1), (0 : Fin 1)) =
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 ∧
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData.exponentMinimum =
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 ∧
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData.countInChartAtRatio
        (((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2)
        (0 : Fin 1) = 1 ∧
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData.minCountInChart (0 : Fin 1) = 1 ∧
    (case2DisplayedCenterSqFormalJacobianChartCertificate
      (K := K) n hS hcont).exponentData.exponentOrder = 1 := by
  let B := localExponentCoordinateBridge cert
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · exact B.ratioAt_eq_centerCard_div_two
  · exact exponentData_exponentMinimum_eq_centerCard_div_two (K := K) n hS hcont
  · exact exponentData_countInChartAtRatio_centerCard_div_two_eq_one
      (K := K) n hS hcont (0 : Fin 1)
  · exact exponentData_minCountInChart_eq_one (K := K) n hS hcont (0 : Fin 1)
  · exact exponentData_exponentOrder_eq_one (K := K) n hS hcont

end case2DisplayedCenterSqFormalJacobianChartCertificate

end Aoyagi
end DLN
end DLNFibre
