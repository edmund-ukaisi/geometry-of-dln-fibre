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

/-- Target chart point on a finite selected-entry chart overlap.

Starting from source chart coordinates `(u, residual)` in chart `sourceChart`,
this constructs the target-chart coordinates in chart `targetChart` by using
the normalized target coordinate as denominator.  The construction is finite
chart algebra only; the associated chart-map equality requires the normalized
target coordinate to be nonzero. -/
def sourceChartTransitionPoint
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (sourceChart targetChart : Fin center.card)
    (u : K) (residual : ι → K) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).ChartPoint targetChart :=
  let denom :=
    selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
      (chartEquiv targetChart).1
  sourceChartPoint hcenter chartEquiv targetChart (u * denom)
    (fun i ↦
      selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual i / denom)

/-- The self-transition of a finite selected-entry chart point is the original
source chart point.

This is a chart-point identity for the finite selected-entry coordinates; it is
not analytic transition regularity or chart coverage. -/
@[simp] theorem sourceChartTransitionPoint_self
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (c : Fin center.card) (u : K) (residual : ι → K) :
    sourceChartTransitionPoint hcenter chartEquiv c c u residual =
      sourceChartPoint hcenter chartEquiv c u residual := by
  apply Prod.ext
  · simp [sourceChartTransitionPoint, sourceChartPoint,
      selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint,
      selectedEntryNormalizedMap]
  · funext p
    have hpne : p.1 ≠ (chartEquiv c).1 := (Finset.mem_erase.mp p.2).1
    simp [sourceChartTransitionPoint, sourceChartPoint,
      selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint,
      selectedEntryNormalizedMap, hpne]

/-- The finite selected-entry transition point is inverted by the reverse
transition on the normalized target-coordinate overlap.

This is a chart-point identity for finite selected-entry coordinates.  It is
not analytic transition regularity, chart coverage, source production, normal
crossings, pole order, or RLCT extraction. -/
theorem sourceChartTransitionPoint_inverse_of_target_normalized_ne_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (sourceChart targetChart : Fin center.card)
    (u : K) (residual : ι → K)
    (htarget :
      selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
        (chartEquiv targetChart).1 ≠ 0) :
    let denom :=
      selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
        (chartEquiv targetChart).1
    let targetResidual : ι → K :=
      fun i ↦ selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual i / denom
    sourceChartTransitionPoint hcenter chartEquiv targetChart sourceChart
        (u * denom) targetResidual =
      sourceChartPoint hcenter chartEquiv sourceChart u residual := by
  dsimp only
  let sourcePivot := (chartEquiv sourceChart).1
  let targetPivot := (chartEquiv targetChart).1
  let denom := selectedEntryNormalizedMap sourcePivot residual targetPivot
  let targetResidual : ι → K :=
    fun i ↦ selectedEntryNormalizedMap sourcePivot residual i / denom
  have hdenom : denom ≠ 0 := by
    simpa [sourcePivot, targetPivot, denom] using htarget
  have hback :
      selectedEntryNormalizedMap targetPivot targetResidual sourcePivot = 1 / denom := by
    have h :=
      selectedEntryNormalizedMap_transition_eq_div_of_target_normalized_ne_zero
        (sourcePivot := sourcePivot) (targetPivot := targetPivot)
        residual hdenom sourcePivot
    simpa [sourcePivot, targetPivot, denom, targetResidual] using h
  change
    sourceChartPoint hcenter chartEquiv sourceChart
        ((u * denom) *
          selectedEntryNormalizedMap targetPivot targetResidual sourcePivot)
        (fun i ↦
          selectedEntryNormalizedMap targetPivot targetResidual i /
            selectedEntryNormalizedMap targetPivot targetResidual sourcePivot) =
      sourceChartPoint hcenter chartEquiv sourceChart u residual
  apply Prod.ext
  · change
      u * denom * selectedEntryNormalizedMap targetPivot targetResidual sourcePivot = u
    rw [hback]
    field_simp [hdenom]
  · funext p
    have hpne : p.1 ≠ sourcePivot := by
      simpa [sourcePivot] using (Finset.mem_erase.mp p.2).1
    have hcoord :
        selectedEntryNormalizedMap targetPivot targetResidual p.1 =
          selectedEntryNormalizedMap sourcePivot residual p.1 / denom := by
      have h :=
        selectedEntryNormalizedMap_transition_eq_div_of_target_normalized_ne_zero
          (sourcePivot := sourcePivot) (targetPivot := targetPivot)
          residual hdenom p.1
      simpa [sourcePivot, targetPivot, denom, targetResidual] using h
    change
      selectedEntryNormalizedMap targetPivot targetResidual p.1 /
          selectedEntryNormalizedMap targetPivot targetResidual sourcePivot =
        residual p.1
    rw [hcoord, hback]
    rw [selectedEntryNormalizedMap_of_ne (pivot := sourcePivot) residual hpne]
    field_simp [hdenom]

/-- Finite selected-entry transition cocycle on a normalized triple overlap.

The two-step chart-point transition from `sourceChart` through `middleChart`
to `targetChart` agrees with the direct transition from `sourceChart` to
`targetChart`, provided the middle and target normalized source coordinates are
nonzero.  This is finite chart-point algebra only; it is not analytic
transition regularity, chart coverage, source production, normal crossings,
pole order, or RLCT extraction. -/
theorem sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (sourceChart middleChart targetChart : Fin center.card)
    (u : K) (residual : ι → K)
    (hmiddle :
      selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
        (chartEquiv middleChart).1 ≠ 0)
    (htarget :
      selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
        (chartEquiv targetChart).1 ≠ 0) :
    let middleDenom :=
      selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
        (chartEquiv middleChart).1
    let middleResidual : ι → K :=
      fun i ↦ selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual i /
        middleDenom
    let middleToTargetDenom :=
      selectedEntryNormalizedMap (chartEquiv middleChart).1 middleResidual
        (chartEquiv targetChart).1
    let middleTargetResidual : ι → K :=
      fun i ↦
        selectedEntryNormalizedMap (chartEquiv middleChart).1 middleResidual i /
          middleToTargetDenom
    sourceChartPoint hcenter chartEquiv targetChart
        ((u * middleDenom) * middleToTargetDenom) middleTargetResidual =
      sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
        u residual := by
  dsimp only
  let sourcePivot := (chartEquiv sourceChart).1
  let middlePivot := (chartEquiv middleChart).1
  let targetPivot := (chartEquiv targetChart).1
  let middleDenom := selectedEntryNormalizedMap sourcePivot residual middlePivot
  let targetDenom := selectedEntryNormalizedMap sourcePivot residual targetPivot
  let middleResidual : ι → K :=
    fun i ↦ selectedEntryNormalizedMap sourcePivot residual i / middleDenom
  let middleToTargetDenom :=
    selectedEntryNormalizedMap middlePivot middleResidual targetPivot
  let middleTargetResidual : ι → K :=
    fun i ↦ selectedEntryNormalizedMap middlePivot middleResidual i / middleToTargetDenom
  have hmiddleDenom : middleDenom ≠ 0 := by
    simpa [sourcePivot, middlePivot, middleDenom] using hmiddle
  have htargetDenom : targetDenom ≠ 0 := by
    simpa [sourcePivot, targetPivot, targetDenom] using htarget
  have hmiddleToTarget :
      middleToTargetDenom = targetDenom / middleDenom := by
    have h :=
      selectedEntryNormalizedMap_transition_eq_div_of_target_normalized_ne_zero
        (sourcePivot := sourcePivot) (targetPivot := middlePivot)
        residual hmiddleDenom targetPivot
    simpa [sourcePivot, middlePivot, targetPivot, middleDenom, targetDenom,
      middleResidual, middleToTargetDenom] using h
  change
    sourceChartPoint hcenter chartEquiv targetChart
        ((u * middleDenom) * middleToTargetDenom) middleTargetResidual =
      sourceChartPoint hcenter chartEquiv targetChart
        (u * targetDenom)
        (fun i ↦ selectedEntryNormalizedMap sourcePivot residual i / targetDenom)
  apply Prod.ext
  · change (u * middleDenom) * middleToTargetDenom = u * targetDenom
    rw [hmiddleToTarget]
    field_simp [hmiddleDenom]
  · funext p
    have hcoord :
        selectedEntryNormalizedMap targetPivot middleTargetResidual p.1 =
          selectedEntryNormalizedMap sourcePivot residual p.1 / targetDenom := by
      have h :=
        selectedEntryNormalizedMap_transition_transition_eq_div_of_ne_zero
          (sourcePivot := sourcePivot) (middlePivot := middlePivot)
          (targetPivot := targetPivot) residual hmiddleDenom htargetDenom p.1
      simpa [sourcePivot, middlePivot, targetPivot, middleDenom, targetDenom,
        middleResidual, middleToTargetDenom, middleTargetResidual] using h
    have hpne : p.1 ≠ targetPivot := by
      simpa [targetPivot] using (Finset.mem_erase.mp p.2).1
    change middleTargetResidual p.1 =
      selectedEntryNormalizedMap sourcePivot residual p.1 / targetDenom
    rw [← selectedEntryNormalizedMap_of_ne
      (pivot := targetPivot) middleTargetResidual hpne]
    exact hcoord

/-- The finite selected-entry target chart point has the same chart map as the
source point on the normalized target-coordinate overlap.

This proves only equality of finite chart maps after constructing the target
chart point.  It is not analytic transition regularity, chart coverage, source
production, normal crossings, pole order, or RLCT extraction. -/
theorem chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (sourceChart targetChart : Fin center.card)
    (u : K) (residual : ι → K)
    (htarget :
      selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
        (chartEquiv targetChart).1 ≠ 0) :
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).chartMap targetChart
        (sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
          u residual) =
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv).chartMap sourceChart
          (sourceChartPoint hcenter chartEquiv sourceChart u residual) := by
  rw [sourceChartTransitionPoint, chartMap_sourceChartPoint_eq,
    chartMap_sourceChartPoint_eq]
  have htransition :
      (fun i ↦
          selectedEntryChartMap (chartEquiv targetChart).1
            (u *
              selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
                (chartEquiv targetChart).1)
            (fun r ↦
              selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual r /
                selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
                  (chartEquiv targetChart).1)
            i) =
        selectedEntryChartMap (chartEquiv sourceChart).1 u residual :=
    selectedEntryChartMap_transition_eq_of_target_normalized_ne_zero
      (sourcePivot := (chartEquiv sourceChart).1)
      (targetPivot := (chartEquiv targetChart).1)
      u residual htarget
  funext i
  exact congrFun htransition i.1

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

/-- The all-pivot selected-entry family covers every finite center value by a
source point written in ambient residual coordinates.

This is the same finite selected-entry inverse as
`exists_chartPoint_chartMap_eq_value`, but with the witness normalized to the
`sourceChartPoint` adapter used by source-coordinate specializations.  It is
not analytic atlas coverage, transition regularity, or source production for
any later recurrence state. -/
theorem exists_sourceChartPoint_chartMap_eq_value
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (value : center → K) :
    ∃ c : Fin center.card, ∃ u : K, ∃ residual : ι → K,
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv).chartMap c
          (sourceChartPoint hcenter chartEquiv c u residual) = value := by
  rcases exists_chartPoint_chartMap_eq_value (K := K) hcenter chartEquiv value with
    ⟨c, x, hx⟩
  rcases x with ⟨u, residualSub⟩
  let pivot := chartEquiv c
  let residual : ι → K := selectedEntryErasedResidual pivot residualSub
  refine ⟨c, u, residual, ?_⟩
  have hpoint :
      sourceChartPoint hcenter chartEquiv c u residual = (u, residualSub) := by
    change
      (u, fun p : ((center.erase (chartEquiv c).1 : Finset ι)) ↦
        selectedEntryErasedResidual pivot residualSub p.1) = (u, residualSub)
    congr
    funext p
    simp [selectedEntryErasedResidual, pivot]
  simpa [hpoint] using hx

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

/-- At a transition-generated target point, the finite loss is the source
selected-entry center square on the normalized target-coordinate overlap.

This is finite selected-entry chart algebra only; it is not analytic
transition regularity, chart coverage, normal crossings, pole order, or RLCT
extraction. -/
theorem loss_sourceChartTransitionPoint_eq_centerSq_of_target_normalized_ne_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (sourceChart targetChart : Fin center.card)
    (u : K) (residual : ι → K)
    (htarget :
      selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
        (chartEquiv targetChart).1 ≠ 0) :
    let C :=
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv
    C.loss
        (C.chartMap targetChart
          (sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
            u residual)) =
      selectedEntryCenterSq center
        (selectedEntryChartMap (chartEquiv sourceChart).1 u residual) := by
  dsimp only
  rw [chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
    hcenter chartEquiv sourceChart targetChart u residual htarget]
  exact loss_sourceChartPoint_eq_centerSq hcenter chartEquiv sourceChart u residual

/-- At a transition-generated target point, the finite loss unit is the target
pivot's normalized center-square factor.

This target unit need not be the source chart's unit. -/
theorem lossUnit_sourceChartTransitionPoint_eq
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (sourceChart targetChart : Fin center.card)
    (u : K) (residual : ι → K) :
    let sourcePivot := chartEquiv sourceChart
    let targetPivot := chartEquiv targetChart
    let denom :=
      selectedEntryNormalizedMap sourcePivot.1 residual targetPivot.1
    let targetResidual : ι → K :=
      fun i ↦ selectedEntryNormalizedMap sourcePivot.1 residual i / denom
    let C :=
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv
    C.lossUnit targetChart
        (sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
          u residual) =
      selectedEntryCenterSqUnitFactor
        (center.erase targetPivot.1) targetResidual := by
  dsimp only
  simpa [sourceChartTransitionPoint] using
    lossUnit_sourceChartPoint_eq hcenter chartEquiv targetChart
      (u *
        selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
          (chartEquiv targetChart).1)
      (fun i ↦
        selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual i /
          selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
            (chartEquiv targetChart).1)

/-- At a transition-generated target point, the finite Jacobian/prior value is
the target pivot-first formal selected-entry determinant.

This remains the formal finite determinant from the microcertificate, not an
analytic volume-form theorem. -/
theorem jacobianPrior_sourceChartTransitionPoint_eq_det
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (sourceChart targetChart : Fin center.card)
    (u : K) (residual : ι → K) :
    let sourcePivot := chartEquiv sourceChart
    let targetPivot := chartEquiv targetChart
    let denom :=
      selectedEntryNormalizedMap sourcePivot.1 residual targetPivot.1
    let targetU := u * denom
    let targetResidual : ι → K :=
      fun i ↦ selectedEntryNormalizedMap sourcePivot.1 residual i / denom
    let C :=
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv
    C.jacobianPrior targetChart
        (sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
          u residual) =
      (selectedEntryPivotFirstJacobian
        (κ := {i // i ∈ center.erase targetPivot.1})
        targetU (fun p ↦ targetResidual p.1)).det := by
  dsimp only
  simpa [sourceChartTransitionPoint] using
    jacobianPrior_sourceChartPoint_eq_det hcenter chartEquiv targetChart
      (u *
        selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
          (chartEquiv targetChart).1)
      (fun i ↦
        selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual i /
          selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
            (chartEquiv targetChart).1)

/-- Source-facing loss monomial identity at a transition-generated target
point on the normalized target-coordinate overlap. -/
theorem loss_monomial_sourceChartTransitionPoint_of_target_normalized_ne_zero
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (sourceChart targetChart : Fin center.card)
    (u : K) (residual : ι → K)
    (htarget :
      selectedEntryNormalizedMap (chartEquiv sourceChart).1 residual
        (chartEquiv targetChart).1 ≠ 0) :
    let C :=
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv
    selectedEntryCenterSq center
        (selectedEntryChartMap (chartEquiv sourceChart).1 u residual) =
      C.lossUnit targetChart
          (sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
            u residual) *
        ∏ j : Fin C.numCoords,
          C.coord targetChart
            (sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
              u residual) j ^
            (2 * C.lossExp targetChart j) := by
  dsimp only
  rw [← loss_sourceChartTransitionPoint_eq_centerSq_of_target_normalized_ne_zero
    hcenter chartEquiv sourceChart targetChart u residual htarget]
  exact
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).loss_monomial targetChart
        (sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
          u residual)

/-- Target-pivot formal Jacobian/prior monomial identity at a
transition-generated target point. -/
theorem jacobianPrior_monomial_sourceChartTransitionPoint
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    (sourceChart targetChart : Fin center.card)
    (u : K) (residual : ι → K) :
    let sourcePivot := chartEquiv sourceChart
    let targetPivot := chartEquiv targetChart
    let denom :=
      selectedEntryNormalizedMap sourcePivot.1 residual targetPivot.1
    let targetU := u * denom
    let targetResidual : ι → K :=
      fun i ↦ selectedEntryNormalizedMap sourcePivot.1 residual i / denom
    let C :=
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv
    (selectedEntryPivotFirstJacobian
        (κ := {i // i ∈ center.erase targetPivot.1})
        targetU (fun p ↦ targetResidual p.1)).det =
      C.jacobianPriorUnit targetChart
          (sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
            u residual) *
        ∏ j : Fin C.numCoords,
          C.coord targetChart
            (sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
              u residual) j ^
            C.jacobianPriorExp targetChart j := by
  dsimp only
  rw [← jacobianPrior_sourceChartTransitionPoint_eq_det
    hcenter chartEquiv sourceChart targetChart u residual]
  exact
    (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := K) hcenter chartEquiv).jacobianPrior_monomial targetChart
        (sourceChartTransitionPoint hcenter chartEquiv sourceChart targetChart
          u residual)

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

private theorem selectedEntryFamily_exists_chartPoint_chartMap_eq_value
    {ι K : Type*} [DecidableEq ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) (value : center → K) :
    ∃ c : Fin (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := K) hcenter chartEquiv).numCharts,
      ∃ x :
        (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
          (K := K) hcenter chartEquiv).ChartPoint c,
        (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
          (K := K) hcenter chartEquiv).chartMap c x = value := by
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  exact exists_chartPoint_chartMap_eq_value (K := K) hcenter chartEquiv value

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

/-- If the cited chart-level extraction hypothesis is supplied for the concrete
Case 2 residual-block all-pivot finite selected-entry certificate, it reports
the finite selected-coordinate count divided by two and local finite order one.

This consumes the extraction hypothesis; it does not construct analytic chart
coverage, transition regularity, source production, global A0 data, or a global
DLN RLCT theorem. -/
theorem lambda_and_poleOrder_eq_selectedCoordinateCount_div_two_and_one_of_extractionHypothesis
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC :
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).ExtractionHypothesis lambda poleOrder) :
    lambda =
        (((prefixMinNat n S - J) * (n (S + 1) - J) : ℕ) : ℚ) / 2 ∧
      poleOrder = 1 := by
  constructor
  · calc
      lambda =
          (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
            (K := K) n hS hcont).exponentData.exponentMinimum :=
        AoyagiNormalCrossingChartCertificate.ExtractionHypothesis.lambda_eq_exponentMinimum hNC
      _ =
          (((prefixMinNat n S - J) * (n (S + 1) - J) : ℕ) : ℚ) / 2 :=
        exponentData_exponentMinimum_eq_selectedCoordinateCount_div_two
          (K := K) n hS hcont
  · calc
      poleOrder =
          (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
            (K := K) n hS hcont).exponentData.exponentOrder :=
        AoyagiNormalCrossingChartCertificate.ExtractionHypothesis.theta_eq_exponentOrder hNC
      _ = 1 :=
        exponentData_exponentOrder_eq_one (K := K) n hS hcont

/-- The Case 2 residual-block all-pivot finite selected-entry family covers
every finite residual-block center value.

This is finite chart-map coverage only.  It is not source production for
arbitrary residual-block pivots, analytic atlas coverage, transition
regularity, normal crossings, pole order, or RLCT extraction. -/
theorem exists_chartPoint_chartMap_eq_value
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (value : {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J} → K) :
    ∃ c : Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts,
      ∃ x :
        (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
          (K := K) n hS hcont).ChartPoint c,
        (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
          (K := K) n hS hcont).chartMap c x = value := by
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
    selectedEntryFamily_exists_chartPoint_chartMap_eq_value
      (K := K)
      (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
      value

/-- The source point in chart `c` of the Case 2 all-pivot selected-entry
certificate, written with the same source residual coordinates used by the
source-selected Case 2 algebra.

This is a finite selected-entry chart point only; it is not source production
for the successor matrix. -/
noncomputable def sourceChartPoint
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).ChartPoint c :=
  selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint
    (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
    (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
    c u residual

/-- In chart `c`, the Case 2 all-pivot selected-entry certificate chart map
at the source point is exactly the source-selected Case 2 chart map for the
pivot enumerated by `c`.

This connects the all-pivot finite normal-crossing microcertificate to the
source-coordinate chart algebra.  It does not claim that Aoyagi displays every
non-top-left pivot chart, and it does not prove chart coverage, source
production, transition regularity, normal crossings, pole order, or RLCT. -/
theorem chartMap_sourceChartPoint_eq_sourceSelectedChartMapOfMem
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).chartMap c
        (sourceChartPoint n hS hcont c u residual) =
      fun p : {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J} ↦
        case2SourceSelectedChartMapOfMem
          ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c).2
          u residual p.1 := by
  simpa [sourceChartPoint, case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2SourceSelectedChartMapOfMem] using
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartPoint_eq
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        c u residual

/-- Target chart point on a Case 2 all-pivot selected-entry overlap.

This is the Case 2 residual-block specialization of the finite selected-entry
transition point.  It constructs chart coordinates only; it does not produce
successor matrices, suffixes, chart coverage, transition regularity, normal
crossings, pole order, or RLCT data. -/
noncomputable def sourceChartTransitionPoint
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).ChartPoint targetChart :=
  selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint
    (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
    (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
    sourceChart targetChart u residual

set_option linter.unnecessarySimpa false in
/-- The self-transition of a Case 2 all-pivot selected-entry chart point is the
original source chart point.

This is finite selected-entry chart-point algebra only; it is not analytic
transition regularity, chart coverage, normal crossings, pole order, or RLCT
extraction. -/
@[simp] theorem sourceChartTransitionPoint_self
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    sourceChartTransitionPoint n hS hcont c c u residual =
      sourceChartPoint n hS hcont c u residual := by
  simpa [sourceChartTransitionPoint, sourceChartPoint,
    case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
    selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_self
      (K := K)
      (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
      c u residual

set_option linter.style.longLine false in
/-- The Case 2 finite selected-entry transition point is inverted by the reverse
transition on the normalized target-coordinate overlap.

This is chart-point algebra for the residual-block all-pivot certificate.  It
does not prove analytic transition regularity, chart coverage, source
production, normal crossings, pole order, or RLCT extraction. -/
theorem sourceChartTransitionPoint_inverse_of_target_normalized_ne_zero
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0) :
    let denom :=
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1
    let targetResidual : ℕ × ℕ → K :=
      fun r ↦
        case2SourceSelectedNormalizedMapOfMem
          ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
            sourceChart).2
          residual r / denom
    sourceChartTransitionPoint n hS hcont targetChart sourceChart
        (u * denom) targetResidual =
      sourceChartPoint n hS hcont sourceChart u residual := by
  simpa [sourceChartTransitionPoint, sourceChartPoint,
    case2SourceSelectedNormalizedMapOfMem,
    case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
    selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_inverse_of_target_normalized_ne_zero
      (K := K)
      (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
      sourceChart targetChart u residual
      (by
        simpa [case2SourceSelectedNormalizedMapOfMem] using htarget)

set_option linter.style.longLine false in
/-- Case 2 finite selected-entry transition cocycle on a normalized triple
overlap.

The two-step chart-point transition from `sourceChart` through `middleChart`
to `targetChart` agrees with the direct transition from `sourceChart` to
`targetChart`, provided the middle and target normalized source coordinates are
nonzero.  This is finite chart-point algebra only; it is not analytic
transition regularity, chart coverage, source production, normal crossings,
pole order, or RLCT extraction. -/
theorem sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart middleChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K)
    (hmiddle :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          middleChart).1 ≠ 0)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0) :
    let middleDenom :=
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          middleChart).1
    let middleResidual : ℕ × ℕ → K :=
      fun i ↦
        case2SourceSelectedNormalizedMapOfMem
          ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
            sourceChart).2
          residual i / middleDenom
    let middleToTargetDenom :=
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          middleChart).2
        middleResidual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1
    let middleTargetResidual : ℕ × ℕ → K :=
      fun i ↦
        case2SourceSelectedNormalizedMapOfMem
          ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
            middleChart).2
          middleResidual i / middleToTargetDenom
    sourceChartPoint n hS hcont targetChart
        ((u * middleDenom) * middleToTargetDenom) middleTargetResidual =
      sourceChartTransitionPoint n hS hcont sourceChart targetChart
        u residual := by
  simpa [sourceChartTransitionPoint, sourceChartPoint,
    case2SourceSelectedNormalizedMapOfMem,
    case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
    selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero
      (K := K)
      (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
      sourceChart middleChart targetChart u residual
      (by
        simpa [case2SourceSelectedNormalizedMapOfMem] using hmiddle)
      (by
        simpa [case2SourceSelectedNormalizedMapOfMem] using htarget)

set_option linter.style.longLine false in
/-- The Case 2 all-pivot target chart point has the same finite residual-center
chart map as the source chart point on the normalized target-coordinate overlap.

This is finite selected-entry transition-point algebra only.  It is not
analytic transition regularity, chart coverage, source production of successor
or suffix data, normal crossings, pole order, or RLCT extraction. -/
theorem chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0) :
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).chartMap targetChart
        (sourceChartTransitionPoint n hS hcont sourceChart targetChart
          u residual) =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).chartMap sourceChart
          (sourceChartPoint n hS hcont sourceChart u residual) := by
  simpa [sourceChartTransitionPoint, sourceChartPoint,
    case2SourceSelectedNormalizedMapOfMem,
    case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
    selectedEntryCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
      (K := K)
      (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
      sourceChart targetChart u residual
      (by
        simpa [case2SourceSelectedNormalizedMapOfMem] using htarget)

/-- Every finite Case 2 residual-block center value is produced by some
source-selected chart of the all-pivot selected-entry family.

The produced chart index chooses a residual-block pivot and the source map is
`case2SourceSelectedChartMapOfMem` for that pivot.  This is finite
selected-entry source-coordinate production only: it is not analytic atlas
coverage, transition regularity, source production of successor matrices or
suffixes, normal crossings, pole order, or RLCT extraction. -/
theorem exists_sourceSelectedChartMap_eq_value
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (value : {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J} → K) :
    ∃ c : Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts,
      ∃ u : K, ∃ residual : ℕ × ℕ → K,
        (fun p : {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J} ↦
          case2SourceSelectedChartMapOfMem
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c).2
            u residual p.1) = value := by
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  rcases exists_sourceChartPoint_chartMap_eq_value
      (K := K)
      (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
      value with
    ⟨c, u, residual, hmap⟩
  refine ⟨c, u, residual, ?_⟩
  rw [← chartMap_sourceChartPoint_eq_sourceSelectedChartMapOfMem
    n hS hcont c u residual]
  exact hmap

/-- Finite overlap formula between two chart-indexed Case 2 source-selected
presentations on the normalised target-coordinate overlap.

If the target chart's normalised residual-block coordinate is nonzero in the
source chart presentation, then the target selected chart with target variable
equal to `u` times that coordinate and residuals obtained by division presents
the same finite residual-block center value.  This is only a finite chart-map
identity: it is not analytic transition regularity, chart coverage,
successor/source production, normal crossings, pole order, or RLCT
extraction. -/
theorem sourceSelected_transition_chartMap_eq_of_target_normalized_ne_zero
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart
    let targetU :=
      u * case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetResidual : ℕ × ℕ → K :=
      fun r ↦
        case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual r /
          case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    (fun p : {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J} ↦
      case2SourceSelectedChartMapOfMem targetPivot.2 targetU targetResidual p.1) =
      fun p : {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J} ↦
        case2SourceSelectedChartMapOfMem sourcePivot.2 u residual p.1 := by
  dsimp only
  exact
    case2SourceSelectedChartMapOfMem_transition_eq_of_target_normalized_ne_zero
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart).2
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart).2
      u residual htarget

/-- Chart-indexed Case 2 form of the denominator-cleared selected-entry
Schur-complement overlap identity.

This is the finite scalar formula attached to the chart-indexed source and
target pivots selected by the all-pivot residual-block certificate.  It proves
only finite selected-entry algebra; it does not prove analytic transition
regularity, chart coverage, successor/following-factor production, normal
crossings, pole order, or RLCT extraction. -/
theorem sourceSelected_schurComplement_transition_mul_sq
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (residual : ℕ × ℕ → K)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0)
    (i : pivotComplement
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart).1.1)
    (j : pivotComplement
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart).1.2) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart
    let denom := case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetResidual : ℕ × ℕ → K :=
      fun r ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual r / denom
    let A : Matrix ℕ ℕ K :=
      fun r c ↦ case2SourceSelectedNormalizedMapOfMem targetPivot.2 targetResidual (r, c)
    denom ^ 2 *
        (pivotFirstD targetPivot.1.1 targetPivot.1.2 A -
          pivotFirstX targetPivot.1.1 targetPivot.1.2 A *
            pivotFirstY targetPivot.1.1 targetPivot.1.2 A) i j =
      denom * case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual (i.1, j.1) -
        case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
            (i.1, targetPivot.1.2) *
          case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
            (targetPivot.1.1, j.1) := by
  dsimp only
  exact
    case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_mul_sq
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart).2
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart).2
      residual htarget i j

/-- Chart-indexed Case 2 residual-block subtype form of the denominator-cleared
selected-entry Schur-complement overlap identity.

This is the same finite scalar formula as
`sourceSelected_schurComplement_transition_mul_sq`, but with the target
lower-right `Q/P` block indexed by the residual-row and residual-column subtype
complements attached to the target chart pivot.  It proves only finite
selected-entry algebra; it does not prove analytic transition regularity, chart
coverage, successor/following-factor production, normal crossings, pole order,
or RLCT extraction. -/
theorem sourceSelectedBlock_schurComplement_transition_mul_sq
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (residual : ℕ × ℕ → K)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0)
    (i : pivotComplement
      (case2ResidualBlockPivotRowOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).2))
    (j : pivotComplement
      (case2ResidualBlockPivotColOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).2)) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart
    let denom := case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetResidual : ℕ × ℕ → K :=
      fun r ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual r / denom
    let row := case2ResidualBlockPivotRowOfMem targetPivot.2
    let col := case2ResidualBlockPivotColOfMem targetPivot.2
    let A := case2SourceSelectedNormalizedBlockOfMem targetPivot.2 targetResidual
    denom ^ 2 *
        (pivotFirstD row col A -
          pivotFirstX row col A * pivotFirstY row col A) i j =
      denom * case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual (i.1.1, j.1.1) -
        case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
            (i.1.1, targetPivot.1.2) *
          case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
            (targetPivot.1.1, j.1.1) := by
  dsimp only
  exact
    case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_mul_sq
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart).2
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart).2
      residual htarget i j

set_option linter.style.longLine false in
/-- Chart-indexed Case 2 residual-block subtype route-independence for the
finite target Schur block.

On a normalized triple overlap, the target lower-right `Q/P` Schur entry
computed after `source -> middle -> target` agrees with the one computed
directly after `source -> target`.  The row and column indices are the
residual-block subtype complements attached to the target chart pivot.  This is
finite selected-entry coordinate algebra only; it is not analytic transition
regularity, chart coverage, source production, normal crossings, pole order, or
RLCT extraction. -/
theorem sourceSelectedBlock_schurComplement_transition_cocycle
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart middleChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (residual : ℕ × ℕ → K)
    (hmiddle :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          middleChart).1 ≠ 0)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0)
    (i : pivotComplement
      (case2ResidualBlockPivotRowOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).2))
    (j : pivotComplement
      (case2ResidualBlockPivotColOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).2)) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let middlePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        middleChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart
    let middleDenom := case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual middlePivot.1
    let targetDenom := case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let middleResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / middleDenom
    let middleToTargetDenom :=
      case2SourceSelectedNormalizedMapOfMem middlePivot.2 middleResidual targetPivot.1
    let middleTargetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem middlePivot.2 middleResidual q /
        middleToTargetDenom
    let directTargetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / targetDenom
    let row := case2ResidualBlockPivotRowOfMem targetPivot.2
    let col := case2ResidualBlockPivotColOfMem targetPivot.2
    let middleA := case2SourceSelectedNormalizedBlockOfMem targetPivot.2 middleTargetResidual
    let directA := case2SourceSelectedNormalizedBlockOfMem targetPivot.2 directTargetResidual
    (pivotFirstD row col middleA -
        pivotFirstX row col middleA * pivotFirstY row col middleA) i j =
      (pivotFirstD row col directA -
        pivotFirstX row col directA * pivotFirstY row col directA) i j := by
  dsimp only
  exact
    case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_cocycle
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart).2
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        middleChart).2
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart).2
      residual hmiddle htarget i j

/-- In chart `c` of the Case 2 all-pivot selected-entry certificate, the
finite residual-block center ideal in source-selected chart-map names is
generated by the selected variable `u`.

This is finite principalization of the selected residual-block center only.
It is not analytic chart coverage, transition regularity, source production,
normal crossings, pole order, or RLCT extraction. -/
theorem centerIdeal_sourceSelectedChartMap_eq_span_singleton
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    let pivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c
    Ideal.span
        {v : K | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
          case2SourceSelectedChartMapOfMem pivot.2 u residual p = v} =
      Ideal.span ({u} : Set K) := by
  dsimp only
  simpa [case2SourceSelectedChartMapOfMem] using
    case2_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c).2
      u residual

/-- In chart `c`, the all-pivot finite certificate's loss at the standard
source point is the Case 2 source-selected finite center square for the pivot
enumerated by `c`. -/
theorem loss_sourceChartPoint_eq_sourceSelectedCenterSq
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    let pivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).loss
        ((case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
          (K := K) n hS hcont).chartMap c
            (sourceChartPoint n hS hcont c u residual)) =
      selectedEntryCenterSq (case2ResidualBlockPivotEntries n S J)
        (case2SourceSelectedChartMapOfMem pivot.2 u residual) := by
  dsimp only
  simpa [sourceChartPoint, case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2SourceSelectedChartMapOfMem] using
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartPoint_eq_centerSq
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        c u residual

/-- In chart `c`, the all-pivot finite certificate's loss unit at the standard
source point is the source-selected normalized center-square factor for the
pivot enumerated by `c`. -/
theorem lossUnit_sourceChartPoint_eq_sourceSelectedUnitFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    let pivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).lossUnit c
        (sourceChartPoint n hS hcont c u residual) =
      selectedEntryCenterSqUnitFactor
        ((case2ResidualBlockPivotEntries n S J).erase pivot.1) residual := by
  dsimp only
  simpa [sourceChartPoint, case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate.lossUnit_sourceChartPoint_eq
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        c u residual

/-- In chart `c`, the all-pivot finite certificate's Jacobian/prior value at
the standard source point is the formal pivot-first selected-entry determinant
for the source-selected pivot enumerated by `c`. -/
theorem jacobianPrior_sourceChartPoint_eq_sourceSelectedDet
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    let pivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).jacobianPrior c
        (sourceChartPoint n hS hcont c u residual) =
      (selectedEntryPivotFirstJacobian
        (κ := {p // p ∈ (case2ResidualBlockPivotEntries n S J).erase pivot.1})
        u (fun p ↦ residual p.1)).det := by
  dsimp only
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  simpa [sourceChartPoint,
    case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
      jacobianPrior_sourceChartPoint_eq_det
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        c u residual

/-- Source-selected presentation of the loss monomial identity in chart `c`
of the Case 2 all-pivot finite certificate. -/
theorem loss_monomial_sourceChartPoint_sourceSelected
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    let pivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c
    selectedEntryCenterSq (case2ResidualBlockPivotEntries n S J)
        (case2SourceSelectedChartMapOfMem pivot.2 u residual) =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).lossUnit c
          (sourceChartPoint n hS hcont c u residual) *
        ∏ j : Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
            (K := K) n hS hcont).numCoords,
          (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
            (K := K) n hS hcont).coord c
            (sourceChartPoint n hS hcont c u residual) j ^
            (2 *
              (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
                (K := K) n hS hcont).lossExp c j) := by
  dsimp only
  simpa [sourceChartPoint, case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2SourceSelectedChartMapOfMem] using
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_monomial_sourceChartPoint
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        c u residual

/-- Source-selected presentation of the formal Jacobian/prior monomial
identity in chart `c` of the Case 2 all-pivot finite certificate. -/
theorem jacobianPrior_monomial_sourceChartPoint_sourceSelected
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    let pivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c
    (selectedEntryPivotFirstJacobian
        (κ := {p // p ∈ (case2ResidualBlockPivotEntries n S J).erase pivot.1})
        u (fun p ↦ residual p.1)).det =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).jacobianPriorUnit c
          (sourceChartPoint n hS hcont c u residual) *
        ∏ j : Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
            (K := K) n hS hcont).numCoords,
          (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
            (K := K) n hS hcont).coord c
            (sourceChartPoint n hS hcont c u residual) j ^
            (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
              (K := K) n hS hcont).jacobianPriorExp c j := by
  dsimp only
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  simpa [sourceChartPoint,
    case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
      jacobianPrior_monomial_sourceChartPoint
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        c u residual

/-- At a transition-generated target chart point, the Case 2 all-pivot finite
certificate's loss is the source-selected finite center square on the
normalized target-coordinate overlap.

This is finite residual-center chart algebra only; it is not analytic
transition regularity, chart coverage, source production, normal crossings,
pole order, or RLCT extraction. -/
theorem loss_sourceChartTransitionPoint_eq_sourceSelectedCenterSq_of_target_normalized_ne_zero
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).loss
        ((case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
          (K := K) n hS hcont).chartMap targetChart
            (sourceChartTransitionPoint n hS hcont sourceChart targetChart
              u residual)) =
      selectedEntryCenterSq (case2ResidualBlockPivotEntries n S J)
        (case2SourceSelectedChartMapOfMem sourcePivot.2 u residual) := by
  dsimp only
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2SourceSelectedChartMapOfMem, case2SourceSelectedNormalizedMapOfMem,
    sourceChartTransitionPoint, sourceChartPoint] using
    loss_sourceChartTransitionPoint_eq_centerSq_of_target_normalized_ne_zero
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart targetChart u residual
        (by simpa [case2SourceSelectedNormalizedMapOfMem] using htarget)

/-- At a transition-generated target chart point, the Case 2 loss unit is the
target pivot's normalized source-selected center-square factor.

This target unit is not asserted to equal the original source chart's unit. -/
theorem lossUnit_sourceChartTransitionPoint_eq_sourceSelectedUnitFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart
    let denom :=
      case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).lossUnit targetChart
        (sourceChartTransitionPoint n hS hcont sourceChart targetChart
          u residual) =
      selectedEntryCenterSqUnitFactor
        ((case2ResidualBlockPivotEntries n S J).erase targetPivot.1)
        targetResidual := by
  dsimp only
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2SourceSelectedNormalizedMapOfMem, sourceChartTransitionPoint,
    sourceChartPoint] using
    lossUnit_sourceChartTransitionPoint_eq
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart targetChart u residual

/-- At a transition-generated target chart point, the Case 2 Jacobian/prior
field is the target pivot-first formal selected-entry determinant.

This is the finite formal determinant from the microcertificate, not an
analytic Jacobian or volume-form theorem. -/
theorem jacobianPrior_sourceChartTransitionPoint_eq_sourceSelectedDet
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart
    let denom :=
      case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetU := u * denom
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).jacobianPrior targetChart
        (sourceChartTransitionPoint n hS hcont sourceChart targetChart
          u residual) =
      (selectedEntryPivotFirstJacobian
        (κ := {p // p ∈ (case2ResidualBlockPivotEntries n S J).erase targetPivot.1})
        targetU (fun p ↦ targetResidual p.1)).det := by
  dsimp only
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2SourceSelectedNormalizedMapOfMem, sourceChartTransitionPoint,
    sourceChartPoint] using
    jacobianPrior_sourceChartTransitionPoint_eq_det
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart targetChart u residual

/-- Source-selected loss monomial identity for a transition-generated target
chart point on the normalized target-coordinate overlap. -/
theorem loss_monomial_sourceChartTransitionPoint_sourceSelected_of_target_normalized_ne_zero
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    selectedEntryCenterSq (case2ResidualBlockPivotEntries n S J)
        (case2SourceSelectedChartMapOfMem sourcePivot.2 u residual) =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).lossUnit targetChart
          (sourceChartTransitionPoint n hS hcont sourceChart targetChart
            u residual) *
        ∏ j : Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
            (K := K) n hS hcont).numCoords,
          (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
            (K := K) n hS hcont).coord targetChart
            (sourceChartTransitionPoint n hS hcont sourceChart targetChart
              u residual) j ^
            (2 *
              (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
                (K := K) n hS hcont).lossExp targetChart j) := by
  dsimp only
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2SourceSelectedChartMapOfMem, case2SourceSelectedNormalizedMapOfMem,
    sourceChartTransitionPoint, sourceChartPoint] using
    loss_monomial_sourceChartTransitionPoint_of_target_normalized_ne_zero
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart targetChart u residual
        (by simpa [case2SourceSelectedNormalizedMapOfMem] using htarget)

/-- Target-pivot formal Jacobian/prior monomial identity for a
transition-generated Case 2 chart point. -/
theorem jacobianPrior_monomial_sourceChartTransitionPoint_sourceSelected
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart
    let denom :=
      case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetU := u * denom
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    (selectedEntryPivotFirstJacobian
        (κ := {p // p ∈ (case2ResidualBlockPivotEntries n S J).erase targetPivot.1})
        targetU (fun p ↦ targetResidual p.1)).det =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).jacobianPriorUnit targetChart
          (sourceChartTransitionPoint n hS hcont sourceChart targetChart
            u residual) *
        ∏ j : Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
            (K := K) n hS hcont).numCoords,
          (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
            (K := K) n hS hcont).coord targetChart
            (sourceChartTransitionPoint n hS hcont sourceChart targetChart
              u residual) j ^
            (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
              (K := K) n hS hcont).jacobianPriorExp targetChart j := by
  dsimp only
  open selectedEntryCenterSqFormalJacobianChartFamilyCertificate in
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate,
    case2SourceSelectedNormalizedMapOfMem, sourceChartTransitionPoint,
    sourceChartPoint] using
    jacobianPrior_monomial_sourceChartTransitionPoint
        (K := K)
        (case2ResidualBlockPivotEntries_nonempty_of_cont n hS hcont)
        (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart targetChart u residual

/-- A chart index of the Case 2 all-pivot selected-entry certificate
instantiates the existing source-selected supplied-boundary constructor at
the pivot enumerated by that chart.

This removes only the manual resupply of the pivot membership already chosen
by the all-pivot chart family.  The chart-family regularity predicates remain
supplied, and this is not chart coverage, source production, normal crossings,
pole order, or RLCT extraction. -/
theorem sourceSelectedBoundary_of_chart_case2Succ_updateSelected
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J K) (u : K)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular) :
    let pivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c
    Case2SourceSelectedSuppliedChartFamilyBoundary K L n S J pivot.1
      t
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      numerator
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      leastValue
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue)
      pre (pre.case2Succ u) u ChartRegular TransitionRegular := by
  dsimp only
  exact
    Case2SourceSelectedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected
      pre u hS hSL hcont
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)) c).2
      exponentPre levelInv leastValueGap chartFamily

/-- The source-selected `Q/P` source-chart-map identity for the pivot selected
by a chart of the Case 2 all-pivot selected-entry certificate.

The theorem is the existing supplied-boundary projection after instantiating
the boundary at the chart-selected pivot.  It does not prove that Aoyagi
displays non-top-left pivot charts, chart coverage, chart-produced post-data,
normal crossings, pole order, or RLCT extraction. -/
theorem sourceSelectedQP_sourceChartMap_of_chart_case2Succ_updateSelected
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J K) (u : K)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (c :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → K) (C : ℕ → τ → K) :
    let data :=
      sourceSelectedBoundary_of_chart_case2Succ_updateSelected
        (K := K) (L := L) (n := n) (S := S) (J := J)
        (t := t) (numerator := numerator) (leastValue := leastValue)
        pre u hS hSL hcont c exponentPre levelInv leastValueGap
        chartFamily
    let row := case2ResidualBlockPivotRowOfMem data.pivot_mem
    let col := case2ResidualBlockPivotColOfMem data.pivot_mem
    let A := case2SourceSelectedNormalizedBlockOfMem data.pivot_mem residual
    let Csrc := case2SourceSelectedFollowingFactorOfMem data.pivot_mem C
    let Ctr :=
      case2SourceSelectedTransportedFollowingFactorOfMem data.pivot_mem residual C
    ∃ q : pivotComplement row → K,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (Matrix.diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2SourceSelectedSubstitutionBlockOfMem data.pivot_mem u residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          Csrc =
        (weightedPivotDiagonal
            ((pre.case2Succ u).weight (case2ResidualRowLevel n S J row))
            (fun i : pivotComplement row ↦
              (pre.case2Succ u).weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD row col A - pivotFirstX row col A * pivotFirstY row col A)) *
          Ctr := by
  exact
    (sourceSelectedBoundary_of_chart_case2Succ_updateSelected
      (K := K) (L := L) (n := n) (S := S) (J := J)
      (t := t) (numerator := numerator) (leastValue := leastValue)
      pre u hS hSL hcont c exponentPre levelInv leastValueGap
      chartFamily).sourceSelectedQP_sourceChartMap residual C

set_option linter.style.longLine false in
/-- Transition-generated target chart data packaged with the supplied
source-selected `Q/P` identity and its finite Schur-overlap formula.

Starting from source chart coordinates `(u, residual)` and a target chart with
nonzero normalized target coordinate, this records three finite facts for the
same transition-generated target data: the target chart point has the same
finite chart map as the source point; the existing supplied target-pivot `Q/P`
identity applies to the transition-generated selected variable and residuals;
and the lower-right target Schur block satisfies the denominator-cleared
selected-entry formula.  This is finite coordinate algebra only; it is not
analytic transition regularity, chart coverage, source production, normal
crossings, pole order, or RLCT extraction. -/
theorem sourceChartTransitionPoint_sourceSelectedQP_package_of_target_normalized_ne_zero
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J K) (u : K)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → K) (C : ℕ → τ → K)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart
    let denom := case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetU := u * denom
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).chartMap targetChart
        (sourceChartTransitionPoint n hS hcont sourceChart targetChart u residual) =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).chartMap sourceChart
          (sourceChartPoint n hS hcont sourceChart u residual)
    ∧
    (let data :=
      sourceSelectedBoundary_of_chart_case2Succ_updateSelected
        (K := K) (L := L) (n := n) (S := S) (J := J)
        (t := t) (numerator := numerator) (leastValue := leastValue)
        pre targetU hS hSL hcont targetChart exponentPre levelInv leastValueGap
        chartFamily
    let row := case2ResidualBlockPivotRowOfMem data.pivot_mem
    let col := case2ResidualBlockPivotColOfMem data.pivot_mem
    let A := case2SourceSelectedNormalizedBlockOfMem data.pivot_mem targetResidual
    let Csrc := case2SourceSelectedFollowingFactorOfMem data.pivot_mem C
    let Ctr :=
      case2SourceSelectedTransportedFollowingFactorOfMem data.pivot_mem targetResidual C
    ∃ q : pivotComplement row → K,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (Matrix.diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2SourceSelectedSubstitutionBlockOfMem data.pivot_mem targetU
              targetResidual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          Csrc =
        (weightedPivotDiagonal
            ((pre.case2Succ targetU).weight (case2ResidualRowLevel n S J row))
            (fun i : pivotComplement row ↦
              (pre.case2Succ targetU).weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD row col A - pivotFirstX row col A * pivotFirstY row col A)) *
          Ctr)
    ∧
    (∀ (i : pivotComplement
          (case2ResidualBlockPivotRowOfMem targetPivot.2))
        (j : pivotComplement
          (case2ResidualBlockPivotColOfMem targetPivot.2)),
      let row := case2ResidualBlockPivotRowOfMem targetPivot.2
      let col := case2ResidualBlockPivotColOfMem targetPivot.2
      let A := case2SourceSelectedNormalizedBlockOfMem targetPivot.2 targetResidual
      denom ^ 2 *
          (pivotFirstD row col A -
            pivotFirstX row col A * pivotFirstY row col A) i j =
        denom * case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual (i.1.1, j.1.1) -
          case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
              (i.1.1, targetPivot.1.2) *
            case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
              (targetPivot.1.1, j.1.1)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact
      chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
        n hS hcont sourceChart targetChart u residual htarget
  · exact
      sourceSelectedQP_sourceChartMap_of_chart_case2Succ_updateSelected
        pre
        (u *
          case2SourceSelectedNormalizedMapOfMem
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
              sourceChart).2
            residual
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
              targetChart).1)
        hS hSL hcont targetChart exponentPre levelInv leastValueGap
        chartFamily
        (fun q ↦
          case2SourceSelectedNormalizedMapOfMem
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
              sourceChart).2
            residual q /
              case2SourceSelectedNormalizedMapOfMem
                ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                  sourceChart).2
                residual
                ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                  targetChart).1)
        C
  · intro i j
    exact
      sourceSelectedBlock_schurComplement_transition_mul_sq
        n hS hcont sourceChart targetChart residual htarget i j

set_option linter.style.longLine false in
/-- Substitution-block form of the selected-entry transition for chart-family
indices.

Starting from source chart coordinates `(u, residual)` and a target chart with
nonzero source-normalised target coordinate, the transition-generated target
selected variable `targetU = u*d` and target residuals `x_/d` give the same
finite source-coordinate substitution block as the original source chart.
This is finite residual-block algebra only; it is not the target Schur-block
rewrite, analytic transition regularity, chart coverage, source production,
normal crossings, pole order, or RLCT extraction. -/
theorem sourceChartTransitionPoint_sourceSelectedSubstitutionBlock_eq_of_target_normalized_ne_zero
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ → ℕ} {S J : ℕ}
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (u : K) (residual : ℕ × ℕ → K)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart
    let denom := case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    case2SourceSelectedSubstitutionBlockOfMem targetPivot.2 (u * denom) targetResidual =
      case2SourceSelectedSubstitutionBlockOfMem sourcePivot.2 u residual := by
  dsimp only
  exact
    case2SourceSelectedSubstitutionBlockOfMem_transition_eq_of_target_normalized_ne_zero
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart).2
      ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart).2
      u residual htarget

set_option linter.style.longLine false in
/-- Transition-generated target chart data packaged with a source-facing
substitution block on the left side of the target-pivot `Q/P` identity.

This refines
`sourceChartTransitionPoint_sourceSelectedQP_package_of_target_normalized_ne_zero`
by using the finite substitution-block transition equality to rewrite only the
left substituted residual block from the transition-generated target chart
back to the original source chart.  The target normalised block, transported
following factor, and denominator-cleared Schur formula remain target-pivot
objects.  This is finite coordinate algebra only; it is not source production
of successor matrices or suffixes, analytic transition regularity, chart
coverage, normal crossings, pole order, or RLCT extraction. -/
theorem sourceChartTransitionPoint_sourceSelectedQP_sourceSubstitution_package_of_target_normalized_ne_zero
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J K) (u : K)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (sourceChart targetChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → K) (C : ℕ → τ → K)
    (htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          targetChart).1 ≠ 0) :
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        targetChart
    let denom := case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetU := u * denom
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).chartMap targetChart
        (sourceChartTransitionPoint n hS hcont sourceChart targetChart u residual) =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).chartMap sourceChart
          (sourceChartPoint n hS hcont sourceChart u residual)
    ∧
    case2SourceSelectedSubstitutionBlockOfMem targetPivot.2 targetU targetResidual =
      case2SourceSelectedSubstitutionBlockOfMem sourcePivot.2 u residual
    ∧
    (let data :=
      sourceSelectedBoundary_of_chart_case2Succ_updateSelected
        (K := K) (L := L) (n := n) (S := S) (J := J)
        (t := t) (numerator := numerator) (leastValue := leastValue)
        pre targetU hS hSL hcont targetChart exponentPre levelInv leastValueGap
        chartFamily
    let row := case2ResidualBlockPivotRowOfMem data.pivot_mem
    let col := case2ResidualBlockPivotColOfMem data.pivot_mem
    let A := case2SourceSelectedNormalizedBlockOfMem data.pivot_mem targetResidual
    let Csrc := case2SourceSelectedFollowingFactorOfMem data.pivot_mem C
    let Ctr :=
      case2SourceSelectedTransportedFollowingFactorOfMem data.pivot_mem targetResidual C
    ∃ q : pivotComplement row → K,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (Matrix.diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2SourceSelectedSubstitutionBlockOfMem sourcePivot.2 u residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          Csrc =
        (weightedPivotDiagonal
            ((pre.case2Succ targetU).weight (case2ResidualRowLevel n S J row))
            (fun i : pivotComplement row ↦
              (pre.case2Succ targetU).weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD row col A - pivotFirstX row col A * pivotFirstY row col A)) *
          Ctr)
    ∧
    (∀ (i : pivotComplement
          (case2ResidualBlockPivotRowOfMem targetPivot.2))
        (j : pivotComplement
          (case2ResidualBlockPivotColOfMem targetPivot.2)),
      let row := case2ResidualBlockPivotRowOfMem targetPivot.2
      let col := case2ResidualBlockPivotColOfMem targetPivot.2
      let A := case2SourceSelectedNormalizedBlockOfMem targetPivot.2 targetResidual
      denom ^ 2 *
          (pivotFirstD row col A -
            pivotFirstX row col A * pivotFirstY row col A) i j =
        denom * case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual (i.1.1, j.1.1) -
          case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
              (i.1.1, targetPivot.1.2) *
            case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
              (targetPivot.1.1, j.1.1)) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
        n hS hcont sourceChart targetChart u residual htarget
  · exact
      sourceChartTransitionPoint_sourceSelectedSubstitutionBlock_eq_of_target_normalized_ne_zero
        hS hcont sourceChart targetChart u residual htarget
  · have hsub :=
      sourceChartTransitionPoint_sourceSelectedSubstitutionBlock_eq_of_target_normalized_ne_zero
        hS hcont sourceChart targetChart u residual htarget
    have hqp :=
      sourceSelectedQP_sourceChartMap_of_chart_case2Succ_updateSelected
        pre
        (u *
          case2SourceSelectedNormalizedMapOfMem
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
              sourceChart).2
            residual
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
              targetChart).1)
        hS hSL hcont targetChart exponentPre levelInv leastValueGap
        chartFamily
        (fun q ↦
          case2SourceSelectedNormalizedMapOfMem
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
              sourceChart).2
            residual q /
              case2SourceSelectedNormalizedMapOfMem
                ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                  sourceChart).2
                residual
                ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                  targetChart).1)
        C
    rcases hqp with ⟨q, hq⟩
    exact ⟨q, by simpa [hsub] using hq⟩
  · intro i j
    exact
      sourceSelectedBlock_schurComplement_transition_mul_sq
        n hS hcont sourceChart targetChart residual htarget i j

/-- The chart index of the displayed top-left Case 2 pivot `(J+1,J+1)` inside
the all-pivot selected-entry certificate.

This is only a finite indexing choice.  It does not assert that the displayed
chart covers all source points or that Aoyagi printed every all-pivot chart. -/
noncomputable def displayedChartIndex
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).numCharts := by
  classical
  simpa [case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate] using
    (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)).symm
      ⟨(J + 1, J + 1),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont⟩

@[simp] theorem finsetSubtypeChartEquiv_displayedChartIndex
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J)
      (displayedChartIndex (K := K) n hS hcont)).1 = (J + 1, J + 1) := by
  classical
  simp [displayedChartIndex]

/-- The displayed source-substitution block is the supplied selected-entry
substitution block for the displayed pivot `(J+1,J+1)`.

This is only a finite notation adapter between the displayed API and the
arbitrary selected-entry API. -/
theorem case2DisplayedSourceSubstitutionBlock_eq_sourceSelectedSubstitutionBlockOfMem_displayed
    {R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    case2DisplayedSourceSubstitutionBlock n hS hcont u residual =
      case2SourceSelectedSubstitutionBlockOfMem
        (case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont)
        u residual := by
  rfl

set_option linter.style.longLine false in
/-- Transition-generated displayed substitution block rewritten to an
arbitrary source selected-entry substitution block.

This is the displayed-pivot specialization of the elementary selected-entry
transition formula.  The denominator is the source-normalized displayed
coordinate `x_(J+1,J+1)`, not the finite center value. -/
theorem case2DisplayedSourceSubstitutionBlock_transition_eq_sourceSelectedSubstitutionBlockOfMem_of_displayed_normalized_ne_zero
    {K : Type*} [Field K]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {sourcePivot : ℕ × ℕ}
    (hsource : sourcePivot ∈ case2ResidualBlockPivotEntries n S J)
    (u : K) (residual : ℕ × ℕ → K)
    (hdisplayed :
      case2SourceSelectedNormalizedMapOfMem hsource residual (J + 1, J + 1) ≠ 0) :
    let denom := case2SourceSelectedNormalizedMapOfMem hsource residual (J + 1, J + 1)
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem hsource residual q / denom
    case2DisplayedSourceSubstitutionBlock n hS hcont (u * denom) targetResidual =
      case2SourceSelectedSubstitutionBlockOfMem hsource u residual := by
  dsimp only
  ext i j
  simpa [case2DisplayedSourceSubstitutionBlock, case2DisplayedSourceChartMap,
    case2SourceSelectedSubstitutionBlockOfMem, case2SourceSelectedChartMapOfMem,
    case2SourceSelectedNormalizedMapOfMem] using
    congrFun
      (selectedEntryChartMap_transition_eq_of_target_normalized_ne_zero
        (sourcePivot := sourcePivot) (targetPivot := (J + 1, J + 1))
        (u := u) (residual := residual)
        (by simpa [case2SourceSelectedNormalizedMapOfMem] using hdisplayed))
      (i.1, j.1)

set_option linter.style.longLine false in
/-- Transition an arbitrary all-pivot Case 2 source chart to the displayed
top-left chart and feed the transition-generated displayed data into the
finite source-chart frontier package.

On the overlap where the displayed normalized coordinate is nonzero, the
displayed target chart point has the same finite chart map as the original
source chart point.  The theorem then packages the existing displayed
frontier data for the transition-generated displayed coordinates
`targetU = u*d` and `targetResidual q = x_q/d`.

This is finite selected-entry/source-frontier algebra only.  It is not an
analytic transition-regularity theorem, chart coverage, source-displayed
all-pivot atlas, source production of successor matrices or suffixes, normal
crossings, pole order, or RLCT extraction. -/
theorem sourceChartTransitionPoint_displayed_frontierBoundaryPackages_of_displayed_normalized_ne_zero
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J K) (u : K)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (sourceChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    (residual : ℕ × ℕ → K)
    (hdisplayed :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual (J + 1, J + 1) ≠ 0) :
    let displayedChart := displayedChartIndex (K := K) n hS hcont
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let denom :=
      case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual (J + 1, J + 1)
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).chartMap displayedChart
        (sourceChartTransitionPoint n hS hcont sourceChart displayedChart u residual) =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).chartMap sourceChart
          (sourceChartPoint n hS hcont sourceChart u residual)
    ∧
    SourceChartFrontierBoundaryPackages K L n S J t numerator leastValue
      pre (u * denom) targetResidual hS hcont := by
  dsimp only
  refine ⟨?_, ?_⟩
  · exact
      chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
        n hS hcont sourceChart (displayedChartIndex (K := K) n hS hcont)
        u residual (by simpa using hdisplayed)
  · exact
      sourceChartMap_frontierBoundaryPackages_withoutChartFamily
        pre
        (u *
          case2SourceSelectedNormalizedMapOfMem
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
              sourceChart).2
            residual (J + 1, J + 1))
        (fun q ↦
          case2SourceSelectedNormalizedMapOfMem
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
              sourceChart).2
            residual q /
              case2SourceSelectedNormalizedMapOfMem
                ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                  sourceChart).2
                residual (J + 1, J + 1))
        hS hSL hcont exponentPre levelInv leastValueGap

set_option linter.style.longLine false in
/-- Continuing-branch version of
`sourceChartTransitionPoint_displayed_frontierBoundaryPackages_of_displayed_normalized_ne_zero`.

After transitioning an arbitrary all-pivot source chart to the displayed
top-left chart on the displayed-coordinate overlap, the
transition-generated displayed data satisfy the existing finite continuing
reindexed source-chart certificate.  The successor following factor in that
certificate is the formula-level displayed successor factor; this theorem does
not construct analytic charts, source-produce a global successor object, prove
coverage, normal crossings, pole order, or RLCT extraction. -/
theorem sourceChartTransitionPoint_displayed_continuingCertificate_of_displayed_normalized_ne_zero
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J K) (u : K)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (sourceChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    (residual : ℕ × ℕ → K) (C : ℕ → τ → K)
    (hdisplayed :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual (J + 1, J + 1) ≠ 0) :
    let displayedChart := displayedChartIndex (K := K) n hS hcont
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let denom :=
      case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual (J + 1, J + 1)
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).chartMap displayedChart
        (sourceChartTransitionPoint n hS hcont sourceChart displayedChart u residual) =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).chartMap sourceChart
          (sourceChartPoint n hS hcont sourceChart u residual)
    ∧
    Case2DisplayedContinuingReindexedSourceChartCertificate
      L n S J t numerator leastValue pre (u * denom) targetResidual hS hcont C := by
  dsimp only
  refine ⟨?_, ?_⟩
  · exact
      chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
        n hS hcont sourceChart (displayedChartIndex (K := K) n hS hcont)
        u residual (by simpa using hdisplayed)
  · exact
      sourceChartMap_continuingReindexedSourceChartCertificate_withoutChartFamily
        pre
        (u *
          case2SourceSelectedNormalizedMapOfMem
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
              sourceChart).2
            residual (J + 1, J + 1))
        (fun q ↦
          case2SourceSelectedNormalizedMapOfMem
            ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
              sourceChart).2
            residual q /
              case2SourceSelectedNormalizedMapOfMem
                ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                  sourceChart).2
                residual (J + 1, J + 1))
        hS hSL hcont hnext exponentPre levelInv leastValueGap C

set_option maxHeartbeats 800000 in
-- The displayed wrapper restates the large dependent `Q/P` package at the
-- displayed chart and elaboration unfolds several finite-index definitions.
set_option linter.style.longLine false in
/-- Displayed specialization of the transition-generated `Q/P`
source-substitution package, bundled with the displayed source-chart frontier.

The target chart is the displayed pivot `(J+1,J+1)`.  On the overlap where the
displayed normalized coordinate is nonzero, this records the finite chart-map
equality, the substitution-block equality, the target-pivot `Q/P` identity
with only its left substituted block rewritten to the original source block,
the denominator-cleared displayed Schur formula, and the displayed frontier
package for the same transition-generated displayed data.  It is finite
selected-entry/source-frontier packaging only; it is not analytic transition
regularity, coverage, source production, normal crossings, pole order, or
RLCT extraction. -/
theorem sourceChartTransitionPoint_displayed_QP_sourceSubstitution_frontierBoundaryPackages_of_displayed_normalized_ne_zero
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J K) (u : K)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (sourceChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → K) (C : ℕ → τ → K)
    (hdisplayed :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual (J + 1, J + 1) ≠ 0) :
    let displayedChart := displayedChartIndex (K := K) n hS hcont
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        displayedChart
    let denom := case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetU := u * denom
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).chartMap displayedChart
        (sourceChartTransitionPoint n hS hcont sourceChart displayedChart u residual) =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).chartMap sourceChart
          (sourceChartPoint n hS hcont sourceChart u residual)
    ∧
    case2SourceSelectedSubstitutionBlockOfMem targetPivot.2 targetU targetResidual =
      case2SourceSelectedSubstitutionBlockOfMem sourcePivot.2 u residual
    ∧
    (let data :=
      sourceSelectedBoundary_of_chart_case2Succ_updateSelected
        (K := K) (L := L) (n := n) (S := S) (J := J)
        (t := t) (numerator := numerator) (leastValue := leastValue)
        pre targetU hS hSL hcont displayedChart exponentPre levelInv leastValueGap
        chartFamily
    let row := case2ResidualBlockPivotRowOfMem data.pivot_mem
    let col := case2ResidualBlockPivotColOfMem data.pivot_mem
    let A := case2SourceSelectedNormalizedBlockOfMem data.pivot_mem targetResidual
    let Csrc := case2SourceSelectedFollowingFactorOfMem data.pivot_mem C
    let Ctr :=
      case2SourceSelectedTransportedFollowingFactorOfMem data.pivot_mem targetResidual C
    ∃ q : pivotComplement row → K,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (Matrix.diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2SourceSelectedSubstitutionBlockOfMem sourcePivot.2 u residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          Csrc =
        (weightedPivotDiagonal
            ((pre.case2Succ targetU).weight (case2ResidualRowLevel n S J row))
            (fun i : pivotComplement row ↦
              (pre.case2Succ targetU).weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD row col A - pivotFirstX row col A * pivotFirstY row col A)) *
          Ctr)
    ∧
    (∀ (i : pivotComplement
          (case2ResidualBlockPivotRowOfMem targetPivot.2))
        (j : pivotComplement
          (case2ResidualBlockPivotColOfMem targetPivot.2)),
      let row := case2ResidualBlockPivotRowOfMem targetPivot.2
      let col := case2ResidualBlockPivotColOfMem targetPivot.2
      let A := case2SourceSelectedNormalizedBlockOfMem targetPivot.2 targetResidual
      denom ^ 2 *
          (pivotFirstD row col A -
            pivotFirstX row col A * pivotFirstY row col A) i j =
        denom * case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual (i.1.1, j.1.1) -
          case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
              (i.1.1, targetPivot.1.2) *
            case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
              (targetPivot.1.1, j.1.1))
    ∧
    SourceChartFrontierBoundaryPackages K L n S J t numerator leastValue
      pre targetU targetResidual hS hcont := by
  dsimp only
  have htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          (displayedChartIndex (K := K) n hS hcont)).1 ≠ 0 := by
    simpa using hdisplayed
  have hpkg :=
    sourceChartTransitionPoint_sourceSelectedQP_sourceSubstitution_package_of_target_normalized_ne_zero
      pre u hS hSL hcont sourceChart
      (displayedChartIndex (K := K) n hS hcont)
      exponentPre levelInv leastValueGap chartFamily residual C htarget
  have hfrontier :=
    sourceChartTransitionPoint_displayed_frontierBoundaryPackages_of_displayed_normalized_ne_zero
      pre u hS hSL hcont sourceChart exponentPre levelInv leastValueGap residual hdisplayed
  rcases hpkg with ⟨hmap, hsub, hqp, hschur⟩
  rcases hfrontier with ⟨_, hfrontier⟩
  exact ⟨hmap, hsub, hqp, hschur,
    by simpa [finsetSubtypeChartEquiv_displayedChartIndex] using hfrontier⟩

set_option maxHeartbeats 800000 in
-- The continuing wrapper restates the large dependent `Q/P` package at the
-- displayed chart and elaboration unfolds several finite-index definitions.
set_option linter.style.longLine false in
/-- Continuing-branch version of the displayed transition-generated `Q/P`
source-substitution package.

This specializes the arbitrary target-pivot source-substitution `Q/P` package
to the displayed pivot `(J+1,J+1)` and places it on the same
transition-generated displayed data as the continuing reindexed source-chart
certificate.  The continuing certificate is the existing finite displayed
certificate; this theorem does not construct successor source data, suffixes,
analytic transitions, normal crossings, pole order, or RLCT data. -/
theorem sourceChartTransitionPoint_displayed_QP_sourceSubstitution_continuingCertificate_of_displayed_normalized_ne_zero
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J K) (u : K)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (sourceChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → K) (C : ℕ → τ → K)
    (hdisplayed :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual (J + 1, J + 1) ≠ 0) :
    let displayedChart := displayedChartIndex (K := K) n hS hcont
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        displayedChart
    let denom := case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetU := u * denom
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).chartMap displayedChart
        (sourceChartTransitionPoint n hS hcont sourceChart displayedChart u residual) =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).chartMap sourceChart
          (sourceChartPoint n hS hcont sourceChart u residual)
    ∧
    case2SourceSelectedSubstitutionBlockOfMem targetPivot.2 targetU targetResidual =
      case2SourceSelectedSubstitutionBlockOfMem sourcePivot.2 u residual
    ∧
    (let data :=
      sourceSelectedBoundary_of_chart_case2Succ_updateSelected
        (K := K) (L := L) (n := n) (S := S) (J := J)
        (t := t) (numerator := numerator) (leastValue := leastValue)
        pre targetU hS hSL hcont displayedChart exponentPre levelInv leastValueGap
        chartFamily
    let row := case2ResidualBlockPivotRowOfMem data.pivot_mem
    let col := case2ResidualBlockPivotColOfMem data.pivot_mem
    let A := case2SourceSelectedNormalizedBlockOfMem data.pivot_mem targetResidual
    let Csrc := case2SourceSelectedFollowingFactorOfMem data.pivot_mem C
    let Ctr :=
      case2SourceSelectedTransportedFollowingFactorOfMem data.pivot_mem targetResidual C
    ∃ q : pivotComplement row → K,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (Matrix.diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2SourceSelectedSubstitutionBlockOfMem sourcePivot.2 u residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          Csrc =
        (weightedPivotDiagonal
            ((pre.case2Succ targetU).weight (case2ResidualRowLevel n S J row))
            (fun i : pivotComplement row ↦
              (pre.case2Succ targetU).weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD row col A - pivotFirstX row col A * pivotFirstY row col A)) *
          Ctr)
    ∧
    (∀ (i : pivotComplement
          (case2ResidualBlockPivotRowOfMem targetPivot.2))
        (j : pivotComplement
          (case2ResidualBlockPivotColOfMem targetPivot.2)),
      let row := case2ResidualBlockPivotRowOfMem targetPivot.2
      let col := case2ResidualBlockPivotColOfMem targetPivot.2
      let A := case2SourceSelectedNormalizedBlockOfMem targetPivot.2 targetResidual
      denom ^ 2 *
          (pivotFirstD row col A -
            pivotFirstX row col A * pivotFirstY row col A) i j =
        denom * case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual (i.1.1, j.1.1) -
          case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
              (i.1.1, targetPivot.1.2) *
            case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual
              (targetPivot.1.1, j.1.1))
    ∧
    Case2DisplayedContinuingReindexedSourceChartCertificate
      L n S J t numerator leastValue pre targetU targetResidual hS hcont C := by
  dsimp only
  have htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          (displayedChartIndex (K := K) n hS hcont)).1 ≠ 0 := by
    simpa using hdisplayed
  have hpkg :=
    sourceChartTransitionPoint_sourceSelectedQP_sourceSubstitution_package_of_target_normalized_ne_zero
      pre u hS hSL hcont sourceChart
      (displayedChartIndex (K := K) n hS hcont)
      exponentPre levelInv leastValueGap chartFamily residual C htarget
  have hcert :=
    sourceChartTransitionPoint_displayed_continuingCertificate_of_displayed_normalized_ne_zero
      pre u hS hSL hcont hnext sourceChart exponentPre levelInv leastValueGap
      residual C hdisplayed
  rcases hpkg with ⟨hmap, hsub, hqp, hschur⟩
  rcases hcert with ⟨_, hcert⟩
  exact ⟨hmap, hsub, hqp, hschur,
    by simpa [finsetSubtypeChartEquiv_displayedChartIndex] using hcert⟩

set_option maxHeartbeats 800000 in
-- The theorem packages a transition-generated displayed substitution rewrite
-- through the large displayed reindexed-product API.
set_option linter.style.longLine false in
/-- Displayed-overlap reindexed next-source product with the left substitution
block rewritten to the original source selected-entry block.

On the displayed overlap `x_(J+1,J+1) != 0`, this applies the already-proved
displayed reindexed next-source product to the transition-generated displayed
data and rewrites only its left substitution block to the original source
selected substitution block.  The right-hand side remains displayed
transition-generated data with the formula-level successor following factor.
This is finite product bookkeeping only; it is not source production of
`Csucc`, suffixes, successor charts, transition regularity, normal crossings,
pole order, or RLCT extraction. -/
theorem sourceChartTransitionPoint_displayed_reindexedNextSourceProduct_sourceSubstitution_of_displayed_normalized_ne_zero
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J K) (u : K)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (sourceChart :
      Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).numCharts)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    (residual : ℕ × ℕ → K) (C : ℕ → τ → K)
    (hdisplayed :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual (J + 1, J + 1) ≠ 0) :
    let displayedChart := displayedChartIndex (K := K) n hS hcont
    let sourcePivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        sourceChart
    let targetPivot :=
      (finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
        displayedChart
    let denom := case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual targetPivot.1
    let targetU := u * denom
    let targetResidual : ℕ × ℕ → K :=
      fun q ↦ case2SourceSelectedNormalizedMapOfMem sourcePivot.2 residual q / denom
    (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).chartMap displayedChart
        (sourceChartTransitionPoint n hS hcont sourceChart displayedChart u residual) =
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).chartMap sourceChart
          (sourceChartPoint n hS hcont sourceChart u residual)
    ∧
    case2DisplayedSourceSubstitutionBlock n hS hcont targetU targetResidual =
      case2SourceSelectedSubstitutionBlockOfMem sourcePivot.2 u residual
    ∧
    (let upivot :=
      case2DisplayedSourceChartMap n hS hcont targetU targetResidual (J + 1, J + 1)
    let post := pre.case2Succ upivot
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → K,
      Case2DisplayedReindexedNextSourceProductEqWithSubstitutionBlock
        pre targetU targetResidual hS hcont C
        (case2SourceSelectedSubstitutionBlockOfMem sourcePivot.2 u residual) q ∧
      IntroducedLabelExponentCertificates L n S (J + 1)
        (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
        (updateSelectedLabelScalar S (J + 1)
          (((prefixMinNat n S : ℤ) - (J : ℤ)) *
            ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
        (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
      IntroducedLabelLevelInvariants L n S (J + 1)
        post.level
        (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
      case2IntroducedLabelLeastValueGap L n S (J + 1)
        (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
      IntroducedLabelRecurrenceState.case2Gap post) := by
  dsimp only
  have htarget :
      case2SourceSelectedNormalizedMapOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        residual
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          (displayedChartIndex (K := K) n hS hcont)).1 ≠ 0 := by
    simpa using hdisplayed
  have hmap :
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont).chartMap (displayedChartIndex (K := K) n hS hcont)
          (sourceChartTransitionPoint n hS hcont sourceChart
            (displayedChartIndex (K := K) n hS hcont) u residual) =
        (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
          (K := K) n hS hcont).chartMap sourceChart
            (sourceChartPoint n hS hcont sourceChart u residual) :=
    chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
      n hS hcont sourceChart (displayedChartIndex (K := K) n hS hcont)
      u residual htarget
  have hsub :
      case2DisplayedSourceSubstitutionBlock n hS hcont
          (u *
            case2SourceSelectedNormalizedMapOfMem
              ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                sourceChart).2
              residual
              ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                (displayedChartIndex (K := K) n hS hcont)).1)
          (fun q ↦
            case2SourceSelectedNormalizedMapOfMem
              ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                sourceChart).2
              residual q /
                case2SourceSelectedNormalizedMapOfMem
                  ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                    sourceChart).2
                  residual
                  ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                    (displayedChartIndex (K := K) n hS hcont)).1) =
        case2SourceSelectedSubstitutionBlockOfMem
          ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
            sourceChart).2 u residual := by
    simpa [finsetSubtypeChartEquiv_displayedChartIndex] using
      case2DisplayedSourceSubstitutionBlock_transition_eq_sourceSelectedSubstitutionBlockOfMem_of_displayed_normalized_ne_zero
        (K := K) n hS hcont
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2
        u residual hdisplayed
  have hprod :=
    sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData_of_substitutionBlock_eq
      pre
      (u *
        case2SourceSelectedNormalizedMapOfMem
          ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
            sourceChart).2
          residual
          ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
            (displayedChartIndex (K := K) n hS hcont)).1)
      (fun q ↦
        case2SourceSelectedNormalizedMapOfMem
          ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
            sourceChart).2
          residual q /
            case2SourceSelectedNormalizedMapOfMem
              ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                sourceChart).2
              residual
              ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
                (displayedChartIndex (K := K) n hS hcont)).1)
      hS hSL hcont exponentPre levelInv leastValueGap C
      (case2SourceSelectedSubstitutionBlockOfMem
        ((finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J))
          sourceChart).2 u residual)
      hsub
  exact ⟨hmap, hsub, by simpa [case2DisplayedSourceChartMap_pivot] using hprod⟩

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

/-- The Case 1 all-pivot finite selected-entry family covers every finite
Case 1 center-generator value.

This is finite chart-map coverage only.  It is not source production for the
hidden old source label or arbitrary row-strip pivots, analytic atlas coverage,
transition regularity, normal crossings, pole order, or RLCT extraction. -/
theorem exists_chartPoint_chartMap_eq_value
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (value : {g : Case1CenterGenerator //
        g ∈ case1CenterGenerators n S J J1} → K) :
    ∃ c : Fin (case1CenterSqFormalJacobianChartFamilyCertificate
        (K := K) n S J J1).numCharts,
      ∃ x :
        (case1CenterSqFormalJacobianChartFamilyCertificate
          (K := K) n S J J1).ChartPoint c,
        (case1CenterSqFormalJacobianChartFamilyCertificate
          (K := K) n S J J1).chartMap c x = value := by
  simpa [case1CenterSqFormalJacobianChartFamilyCertificate] using
    selectedEntryFamily_exists_chartPoint_chartMap_eq_value
      (K := K)
      (case1CenterGenerators_nonempty n S J J1)
      (finsetSubtypeChartEquiv (case1CenterGenerators n S J J1))
      value

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
