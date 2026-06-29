import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.Jacobian
import DLNFibre.DLN.Aoyagi.BlowupArithmetic
import DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure

/-!
# Selected-entry signed-box monomial-unit measure bridge

This file packages the elementary real selected-entry calculation in the form
expected by the signed-box residual-source measure lemmas.  The coordinate
index is `Option {i // i ∈ center.erase pivot}`: `none` is the selected pivot
coordinate and `some i` are the non-pivot residual coordinates.

The bridge proves chart-side algebra, bounded-unit facts, and the
finite-dimensional weighted pushforward identity for the concrete
center-indexed selected-entry chart.  It does not construct an analytic source
chart, prove source coverage, identify the original DLN source measure,
compare the full source density, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open PaperEndpointFixedBaseRegularCoordinateSourceData

namespace SelectedEntrySignedBox

variable {ι : Type*} [DecidableEq ι]

/-- Signed-box coordinates for one selected-entry chart: `none` is the selected
pivot coordinate and `some i` are the non-pivot center coordinates. -/
abbrev Coord {center : Finset ι} (pivot : center) :=
  Option {i // i ∈ center.erase pivot.1}

/-- Extend signed-box residual coordinates to an ambient residual function on
the finite center's ambient index type. -/
def sourceResidual {center : Finset ι} (pivot : center)
    (y : Coord pivot → ℝ) (i : ι) : ℝ :=
  if h : i ∈ center.erase pivot.1 then y (some ⟨i, h⟩) else 0

/-- The selected-entry residual square-sum after substituting the pivot-first
chart map. -/
def residual {center : Finset ι} (pivot : center)
    (y : Coord pivot → ℝ) : ℝ :=
  selectedEntryCenterSq center
    (selectedEntryChartMap pivot.1 (y none) (sourceResidual pivot y))

/-- The selected-entry residual unit `1 + sum residual_i^2`. -/
def residualUnit {center : Finset ι} (pivot : center)
    (y : Coord pivot → ℝ) : ℝ :=
  selectedEntryCenterSqUnitFactor (center.erase pivot.1)
    (sourceResidual pivot y)

/-- The selected-entry formal density unit for the pivot-first determinant. -/
def densityUnit {center : Finset ι} (pivot : center)
    (_y : Coord pivot → ℝ) : ℝ :=
  1

/-- The formal absolute Jacobian density carried by the selected-entry pivot
coordinate. -/
def sourceDensity {center : Finset ι} (pivot : center)
    (y : Coord pivot → ℝ) : ℝ :=
  |y none| ^ ((center.erase pivot.1).card : ℝ)

/-- The selected-entry source density is the absolute value of the formal
pivot-first determinant. -/
theorem sourceDensity_eq_abs_pivotFirstJacobian_det {center : Finset ι}
    (pivot : center) (y : Coord pivot → ℝ) :
    sourceDensity pivot y =
      |(selectedEntryPivotFirstJacobian
        (κ := {i // i ∈ center.erase pivot.1}) (y none)
        (fun p ↦ sourceResidual pivot y p.1)).det| := by
  rw [selectedEntryPivotFirstJacobian_det]
  simp [sourceDensity, Real.rpow_natCast, abs_pow]

/-- Loss exponents for the selected-entry signed-box coordinates. -/
def lossExp {center : Finset ι} (pivot : center) : Coord pivot → ℕ
  | none => 1
  | some _ => 0

/-- Formal density exponents for the selected-entry signed-box coordinates. -/
def densityExp {center : Finset ι} (pivot : center) : Coord pivot → ℕ
  | none => (center.erase pivot.1).card
  | some _ => 0

/-- Pointwise selected-entry loss monomial-unit identity on signed-box
coordinates. -/
theorem residual_eq_unit_mul_abs_monomial {center : Finset ι} (pivot : center)
    (y : Coord pivot → ℝ) :
    residual pivot y =
      residualUnit pivot y * ∏ i : Coord pivot, |y i| ^ (2 * (lossExp pivot i : ℝ)) := by
  rw [residual, selectedEntryCenterSq_selectedEntryChartMap pivot.2]
  simp [residualUnit, selectedEntryCenterSqUnitFactor, lossExp, Fintype.prod_option,
    pow_two, mul_comm, mul_assoc]

/-- Pointwise selected-entry formal-density monomial-unit identity on
signed-box coordinates. -/
theorem sourceDensity_eq_unit_mul_abs_monomial {center : Finset ι}
    (pivot : center) (y : Coord pivot → ℝ) :
    sourceDensity pivot y =
      densityUnit pivot y * ∏ i : Coord pivot, |y i| ^ (densityExp pivot i : ℝ) := by
  simp [sourceDensity, densityUnit, densityExp, Fintype.prod_option]

/-- The selected-entry residual unit is bounded below by `1`. -/
theorem one_le_residualUnit {center : Finset ι} (pivot : center)
    (y : Coord pivot → ℝ) :
    1 ≤ residualUnit pivot y := by
  rw [residualUnit, selectedEntryCenterSqUnitFactor]
  exact le_add_of_nonneg_right
    (selectedEntryCenterSq_nonneg (center.erase pivot.1) (sourceResidual pivot y))

/-- The selected-entry formal density unit is nonnegative. -/
theorem densityUnit_nonneg {center : Finset ι} (pivot : center)
    (y : Coord pivot → ℝ) :
    0 ≤ densityUnit pivot y := by
  simp [densityUnit]

/-- The selected-entry formal density unit is bounded above by `1`. -/
theorem densityUnit_le_one {center : Finset ι} (pivot : center)
    (y : Coord pivot → ℝ) :
    densityUnit pivot y ≤ 1 := by
  simp [densityUnit]

/-- The selected-entry formal density unit is a.e. measurable on any signed
box with this coordinate index. -/
theorem densityUnit_aemeasurable {center : Finset ι} (pivot : center)
    (R : Coord pivot → ℝ) :
    AEMeasurable (densityUnit pivot)
      (Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i)))) := by
  exact aemeasurable_const

/-- The selected-entry pointwise monomial-unit identities and unit bounds,
packaged as a.e. hypotheses over an arbitrary signed box. -/
theorem monomialUnitHypotheses {center : Finset ι} (pivot : center)
    (R : Coord pivot → ℝ) :
    AEMeasurable (densityUnit pivot)
        (Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i)))) ∧
      (∀ᵐ y : Coord pivot → ℝ
        ∂Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i))),
        residual pivot y =
          residualUnit pivot y * ∏ i, |y i| ^ (2 * (lossExp pivot i : ℝ))) ∧
      (∀ᵐ y : Coord pivot → ℝ
        ∂Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i))),
        sourceDensity pivot y =
          densityUnit pivot y * ∏ i, |y i| ^ (densityExp pivot i : ℝ)) ∧
      (∀ᵐ y : Coord pivot → ℝ
        ∂Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i))),
        1 ≤ residualUnit pivot y) ∧
      (∀ᵐ y : Coord pivot → ℝ
        ∂Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i))),
        0 ≤ densityUnit pivot y) ∧
      (∀ᵐ y : Coord pivot → ℝ
        ∂Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i))),
        densityUnit pivot y ≤ 1) := by
  refine ⟨densityUnit_aemeasurable pivot R, ?_, ?_, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun y => residual_eq_unit_mul_abs_monomial pivot y
  · exact Filter.Eventually.of_forall fun y => sourceDensity_eq_unit_mul_abs_monomial pivot y
  · exact Filter.Eventually.of_forall fun y => one_le_residualUnit pivot y
  · exact Filter.Eventually.of_forall fun y => densityUnit_nonneg pivot y
  · exact Filter.Eventually.of_forall fun y => densityUnit_le_one pivot y

/-- The selected-entry monomial-unit package specialized through the existing
signed-box inequality consumer, with constants `c = C = 1`. -/
theorem monomialLower_sourceDensityBounds {center : Finset ι} (pivot : center)
    (R : Coord pivot → ℝ) :
    AEMeasurable (fun y : Coord pivot → ℝ => ENNReal.ofReal (sourceDensity pivot y))
        (Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i)))) ∧
      (∀ᵐ y : Coord pivot → ℝ
        ∂Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i))),
        1 * ∏ i, |y i| ^ (2 * (lossExp pivot i : ℝ)) ≤ residual pivot y) ∧
      (∀ᵐ y : Coord pivot → ℝ
        ∂Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i))),
        0 ≤ sourceDensity pivot y) ∧
      (∀ᵐ y : Coord pivot → ℝ
        ∂Measure.pi (fun i : Coord pivot => volume.restrict (Set.Ioo (-(R i)) (R i))),
        sourceDensity pivot y ≤ 1 * ∏ i, |y i| ^ (densityExp pivot i : ℝ)) := by
  rcases monomialUnitHypotheses pivot R with
    ⟨hdensityUnit_aemeas, hres_eq, hsourceDensity_eq, hresUnit_lower,
      hdensityUnit_nonneg, hdensityUnit_le⟩
  exact
    signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
      (residual := residual pivot)
      (sourceDensity := sourceDensity pivot)
      (residualUnit := residualUnit pivot)
      (densityUnit := densityUnit pivot)
      (R := R) (h := densityExp pivot) (k := lossExp pivot) (c := 1) (C := 1)
      hdensityUnit_aemeas hres_eq hsourceDensity_eq hresUnit_lower
      hdensityUnit_nonneg hdensityUnit_le

namespace CenterCoord

/-- Center-indexed signed-box residual coordinates.  The chart supplies the
selected pivot separately; this residual value at the pivot is irrelevant to
the chart's pivot branch. -/
def sourceResidual {center : Finset ι}
    (y : center → ℝ) (i : ι) : ℝ :=
  if h : i ∈ center then y ⟨i, h⟩ else 0

/-- The actual center-indexed selected-entry chart map.  The selected pivot
coordinate is sent to itself, and every other center coordinate is multiplied
by the pivot coordinate. -/
def chartMap {center : Finset ι} (pivot : center)
    (y : center → ℝ) : center → ℝ :=
  fun i => selectedEntryChartMap pivot.1 (y pivot) (sourceResidual y) i.1

@[simp] theorem chartMap_pivot {center : Finset ι} (pivot : center)
    (y : center → ℝ) :
    chartMap pivot y pivot = y pivot := by
  simp [chartMap]

theorem chartMap_of_ne {center : Finset ι} (pivot : center)
    (y : center → ℝ) {i : center} (hi : i ≠ pivot) :
    chartMap pivot y i = y pivot * y i := by
  have hne : i.1 ≠ pivot.1 := by
    intro h
    exact hi (Subtype.ext h)
  simp [chartMap, sourceResidual, selectedEntryChartMap, hne, i.2]

set_option linter.style.longLine false in
/-- Aoyagi's displayed Case 2 source-chart map is the center-indexed
selected-entry chart map specialized to the displayed pivot.

This is definitional vocabulary alignment for the old Case 2 center
`case2ResidualBlockPivotEntries n S J`.  It does not identify any post-pivot
factor product with these coordinates. -/
theorem case2DisplayedSourceChartMap_eq_selectedEntrySignedBoxCenterCoord_chartMap_apply
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (y : {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J} → ℝ)
    (p : {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J}) :
    case2DisplayedSourceChartMap n hS hcont
        (y (⟨(J + 1, J + 1),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont⟩ :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J}))
        (SelectedEntrySignedBox.CenterCoord.sourceResidual y) p.1 =
      SelectedEntrySignedBox.CenterCoord.chartMap
        (⟨(J + 1, J + 1),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont⟩ :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S J}) y p :=
  rfl

/-- The selected-entry chart preserves the pivot-zero locus. -/
theorem chartMap_mem_pivot_ne_zero_iff {center : Finset ι} (pivot : center)
    (y : center → ℝ) :
    chartMap pivot y pivot ≠ 0 ↔ y pivot ≠ 0 := by
  simp

/-- If the selected pivot coordinate is zero, the center-indexed
selected-entry chart collapses to the origin. -/
theorem chartMap_eq_zero_of_pivot_eq_zero {center : Finset ι} (pivot : center)
    (y : center → ℝ) (hy : y pivot = 0) :
    chartMap pivot y = 0 := by
  funext i
  by_cases hi : i = pivot
  · subst i
    simp [hy]
  · rw [chartMap_of_ne pivot y hi, hy, zero_mul]
    rfl

/-- The center-coordinate inverse for a fixed selected pivot with nonzero
target value: keep the pivot coordinate and divide every other coordinate by
the pivot. -/
noncomputable def preimageOfPivotNeZero {center : Finset ι} (pivot : center)
    (value : center → ℝ) : center → ℝ :=
  fun i ↦ if i = pivot then value pivot else value i / value pivot

/-- The fixed-pivot center-coordinate inverse maps back to the target value
when the selected pivot coordinate is nonzero. -/
theorem chartMap_preimageOfPivotNeZero {center : Finset ι} (pivot : center)
    (value : center → ℝ) (hpivot : value pivot ≠ 0) :
    chartMap pivot (preimageOfPivotNeZero pivot value) = value := by
  funext i
  by_cases hi : i = pivot
  · subst i
    simp [preimageOfPivotNeZero]
  · have hpivot_value :
        preimageOfPivotNeZero pivot value pivot = value pivot := by
      simp [preimageOfPivotNeZero]
    have hi_value :
        preimageOfPivotNeZero pivot value i = value i / value pivot := by
      simp [preimageOfPivotNeZero, hi]
    rw [chartMap_of_ne pivot (preimageOfPivotNeZero pivot value) hi,
      hpivot_value, hi_value]
    field_simp [hpivot]

/-- On the nonzero-pivot locus, the fixed-pivot center-coordinate inverse is
also a left inverse to the selected-entry chart. -/
theorem preimageOfPivotNeZero_chartMap {center : Finset ι} (pivot : center)
    (y : center → ℝ) (hpivot : y pivot ≠ 0) :
    preimageOfPivotNeZero pivot (chartMap pivot y) = y := by
  funext i
  by_cases hi : i = pivot
  · subst i
    simp [preimageOfPivotNeZero]
  · have hi_chart :
        chartMap pivot y i = y pivot * y i := by
      exact chartMap_of_ne pivot y hi
    simp [preimageOfPivotNeZero, hi, hi_chart, hpivot]

/-- The fixed-pivot center-coordinate inverse is measurable. -/
theorem measurable_preimageOfPivotNeZero {center : Finset ι} (pivot : center) :
    Measurable (preimageOfPivotNeZero pivot) := by
  refine measurable_pi_lambda _ ?_
  intro i
  by_cases hi : i = pivot
  · subst i
    simpa [preimageOfPivotNeZero] using
      (measurable_pi_apply pivot : Measurable fun value : center → ℝ => value pivot)
  · have hfun :
        (fun value : center → ℝ => preimageOfPivotNeZero pivot value i) =
          fun value : center → ℝ => value i / value pivot := by
      funext value
      simp [preimageOfPivotNeZero, hi]
    rw [hfun]
    exact (measurable_pi_apply i).div (measurable_pi_apply pivot)

/-- Existence form of the fixed-pivot center-coordinate inverse. -/
theorem exists_chartMap_eq_value_of_pivot_ne_zero {center : Finset ι}
    (pivot : center) (value : center → ℝ) (hpivot : value pivot ≠ 0) :
    ∃ y : center → ℝ, chartMap pivot y = value :=
  ⟨preimageOfPivotNeZero pivot value,
    chartMap_preimageOfPivotNeZero pivot value hpivot⟩

/-- Matrix form of the fixed-pivot selected-entry inverse: if the matrix entry
corresponding to the selected pivot is nonzero, then the whole matrix is a
selected-entry chart matrix for that pivot after the supplied residual-coordinate
equivalence.

This is finite coordinate algebra only.  It does not prove that a source
construction lands in the chosen nonzero-pivot chart. -/
theorem exists_matrix_eq_chartMap_of_pivot_ne_zero {center : Finset ι}
    (pivot : center) {μ ν : Type*} (D : Matrix μ ν ℝ)
    (residualCoordEquiv : AoyagiResidualBlockCoordinateIndex μ ν ≃ center)
    (hpivot :
      D (residualCoordEquiv.symm pivot).1
        (residualCoordEquiv.symm pivot).2 ≠ 0) :
    ∃ y : center → ℝ,
      D =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex μ ν ↦
            chartMap pivot y (residualCoordEquiv c)) := by
  let value : center → ℝ :=
    fun p ↦ D (residualCoordEquiv.symm p).1 (residualCoordEquiv.symm p).2
  have hpivot_value : value pivot ≠ 0 := by
    simpa [value] using hpivot
  rcases exists_chartMap_eq_value_of_pivot_ne_zero pivot value hpivot_value with
    ⟨y, hy⟩
  refine ⟨y, ?_⟩
  ext i j
  have hcoord := congrFun hy (residualCoordEquiv (i, j))
  simpa [value, AoyagiResidualBlockCoordinateIndex.matrix] using hcoord.symm

set_option linter.style.longLine false in
/-- All-pivot selected-entry inverse in center coordinates: any nonzero
center-coordinate vector belongs to some selected-entry chart image.

This is finite coordinate coverage only.  It does not construct retained-passive
source data or prove that a particular source lands in the nonzero locus. -/
theorem exists_pivot_chartMap_eq_value_of_ne_zero {center : Finset ι}
    (value : center → ℝ) (hvalue : value ≠ 0) :
    ∃ pivot : center, ∃ y : center → ℝ, chartMap pivot y = value := by
  classical
  have hentry : ∃ pivot : center, value pivot ≠ 0 := by
    by_contra hnone
    apply hvalue
    funext pivot
    exact not_not.mp (fun hpivot ↦ hnone ⟨pivot, hpivot⟩)
  rcases hentry with ⟨pivot, hpivot⟩
  rcases exists_chartMap_eq_value_of_pivot_ne_zero pivot value hpivot with
    ⟨y, hy⟩
  exact ⟨pivot, y, hy⟩

set_option linter.style.longLine false in
/-- Matrix form of the all-pivot selected-entry inverse: any nonzero residual
matrix is a selected-entry chart matrix for some pivot after the supplied
residual-coordinate equivalence.

This removes the need to preselect a fixed nonzero pivot at the finite
selected-entry level.  It does not prove retained-passive source production,
factor alignment, measure transport, normal crossings, pole order, or RLCT. -/
theorem exists_pivot_matrix_eq_chartMap_of_ne_zero {center : Finset ι}
    {μ ν : Type*} (D : Matrix μ ν ℝ)
    (residualCoordEquiv : AoyagiResidualBlockCoordinateIndex μ ν ≃ center)
    (hD : D ≠ 0) :
    ∃ pivot : center, ∃ y : center → ℝ,
      D =
        AoyagiResidualBlockCoordinateIndex.matrix
          (fun c : AoyagiResidualBlockCoordinateIndex μ ν ↦
            chartMap pivot y (residualCoordEquiv c)) := by
  classical
  have hentry :
      ∃ c : AoyagiResidualBlockCoordinateIndex μ ν, D c.1 c.2 ≠ 0 := by
    by_contra hnone
    apply hD
    ext i j
    exact not_not.mp (fun hij ↦ hnone ⟨(i, j), hij⟩)
  rcases hentry with ⟨c, hc⟩
  let pivot : center := residualCoordEquiv c
  have hpivot :
      D (residualCoordEquiv.symm pivot).1
        (residualCoordEquiv.symm pivot).2 ≠ 0 := by
    simpa [pivot] using hc
  rcases exists_matrix_eq_chartMap_of_pivot_ne_zero pivot D residualCoordEquiv hpivot with
    ⟨y, hy⟩
  exact ⟨pivot, y, hy⟩

/-- The center-indexed selected-entry chart map is continuous. -/
theorem continuous_chartMap {center : Finset ι} (pivot : center) :
    Continuous (chartMap pivot) := by
  rw [continuous_pi_iff]
  intro i
  by_cases hi : i = pivot
  · subst i
    simpa using (continuous_apply pivot : Continuous fun y : center → ℝ => y pivot)
  · have hfun :
        (fun y : center → ℝ => chartMap pivot y i) =
          fun y : center → ℝ => y pivot * y i := by
      funext y
      exact chartMap_of_ne pivot y hi
    rw [hfun]
    exact (continuous_apply pivot).mul (continuous_apply i)

/-- The center-indexed selected-entry chart map is measurable. -/
theorem measurable_chartMap {center : Finset ι} (pivot : center) :
    Measurable (chartMap pivot) :=
  (continuous_chartMap pivot).measurable

/-- The center-indexed selected-entry chart map is a.e. measurable on any
signed box. -/
theorem aemeasurable_chartMap {center : Finset ι} (pivot : center)
    (R : center → ℝ) :
    AEMeasurable (chartMap pivot)
      (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))) :=
  (measurable_chartMap pivot).aemeasurable

/-- The center-indexed signed box with radii `R`. -/
def signedBoxSet {center : Finset ι} (R : center → ℝ) : Set (center → ℝ) :=
  Set.univ.pi fun i => Set.Ioo (-(R i)) (R i)

/-- The signed-box image of the finite selected-entry chart is the origin
together with the nonzero-pivot horn described by the quotient coordinates. -/
theorem mem_chartMap_image_signedBoxSet_iff {center : Finset ι} (pivot : center)
    {R x : center → ℝ} (hR : ∀ i, 0 < R i) :
    x ∈ chartMap pivot '' signedBoxSet R ↔
      x = 0 ∨
        (x pivot ≠ 0 ∧ |x pivot| < R pivot ∧
          ∀ i : center, i ≠ pivot → |x i / x pivot| < R i) := by
  constructor
  · rintro ⟨y, hybox, rfl⟩
    by_cases hyp : y pivot = 0
    · left
      exact chartMap_eq_zero_of_pivot_eq_zero pivot y hyp
    · right
      refine ⟨?_, ?_, ?_⟩
      · simpa using hyp
      · have hy : y pivot ∈ Set.Ioo (-(R pivot)) (R pivot) :=
          hybox pivot (Set.mem_univ pivot)
        simpa using (abs_lt.mpr hy)
      · intro i hi
        have hy : y i ∈ Set.Ioo (-(R i)) (R i) :=
          hybox i (Set.mem_univ i)
        have hdiv : chartMap pivot y i / chartMap pivot y pivot = y i := by
          rw [chartMap_of_ne pivot y hi, chartMap_pivot]
          field_simp [hyp]
        calc
          |chartMap pivot y i / chartMap pivot y pivot| = |y i| := by rw [hdiv]
          _ < R i := abs_lt.mpr hy
  · intro hx
    rcases hx with rfl | ⟨hpivot, hpivot_lt, hhorn⟩
    · refine ⟨0, ?_, ?_⟩
      · rw [signedBoxSet]
        intro i _hi
        exact abs_lt.mp (by simpa using hR i)
      · exact chartMap_eq_zero_of_pivot_eq_zero pivot (0 : center → ℝ) rfl
    · let y : center → ℝ := fun i =>
        if i = pivot then x pivot else x i / x pivot
      refine ⟨y, ?_, ?_⟩
      · rw [signedBoxSet]
        intro i _hi
        have hyabs : |y i| < R i := by
          by_cases hi : i = pivot
          · subst i
            simpa [y] using hpivot_lt
          · simpa [y, hi] using hhorn i hi
        exact abs_lt.mp hyabs
      · funext i
        by_cases hi : i = pivot
        · subst i
          simp [y]
        · have hmul : x pivot * (x i / x pivot) = x i := by
            field_simp [hpivot]
          rw [chartMap_of_ne pivot y hi]
          simpa [y, hi] using hmul

/-- If a chosen pivot coordinate is nonzero and dominates all absolute
coordinates, then the point lies in that selected-entry chart image whenever
the pivot itself is inside its radius and every non-pivot chart radius is
larger than `1`. -/
theorem mem_chartMap_image_signedBoxSet_of_pivot_abs_max {center : Finset ι}
    (pivot : center) {R x : center → ℝ}
    (hpivot : x pivot ≠ 0) (hpivot_lt : |x pivot| < R pivot)
    (hmax : ∀ i : center, |x i| ≤ |x pivot|)
    (hR_nonpivot : ∀ i : center, i ≠ pivot → 1 < R i) :
    x ∈ chartMap pivot '' signedBoxSet R := by
  rw [mem_chartMap_image_signedBoxSet_iff pivot]
  · right
    refine ⟨hpivot, hpivot_lt, ?_⟩
    intro i hi
    have hpivot_abs_pos : 0 < |x pivot| := abs_pos.mpr hpivot
    have hle_one : |x i| / |x pivot| ≤ 1 := by
      rw [div_le_iff₀ hpivot_abs_pos]
      simpa using hmax i
    calc
      |x i / x pivot| = |x i| / |x pivot| := by rw [abs_div]
      _ ≤ 1 := hle_one
      _ < R i := hR_nonpivot i hi
  · intro i
    by_cases hi : i = pivot
    · subst i
      exact (abs_pos.mpr hpivot).trans hpivot_lt
    · exact zero_lt_one.trans (hR_nonpivot i hi)

omit [DecidableEq ι] in
/-- A nonzero finite coordinate vector has a nonzero coordinate whose absolute
value dominates all coordinates. -/
theorem exists_pivot_abs_le_abs_of_ne_zero {center : Finset ι} [Nonempty center]
    (x : center → ℝ) (hx : x ≠ 0) :
    ∃ pivot : center, x pivot ≠ 0 ∧ ∀ i : center, |x i| ≤ |x pivot| := by
  classical
  obtain ⟨pivot, _hpivot_mem, hpivot_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset center) (fun i => |x i|)
      Finset.univ_nonempty
  refine ⟨pivot, ?_, fun i => hpivot_max i (by simp)⟩
  intro hpivot_zero
  apply hx
  funext i
  have hle_zero : |x i| ≤ 0 := by
    simpa [hpivot_zero] using hpivot_max i (by simp)
  have habs_zero : |x i| = 0 :=
    le_antisymm hle_zero (abs_nonneg _)
  exact abs_eq_zero.mp habs_zero

/-- A nonzero point in a smaller signed box lies in some selected-entry chart
image, by choosing a coordinate of maximal absolute value as pivot.

The strict `1 < R i` condition is what makes tied maximal non-pivot quotients
fit inside the open quotient radii. -/
theorem exists_maxPivot_mem_chartMap_image_signedBoxSet_of_mem_signedBoxSet_ne_zero
    {center : Finset ι} [Nonempty center] {R S x : center → ℝ}
    (hSleR : ∀ i, S i ≤ R i) (hRone : ∀ i, 1 < R i)
    (hxS : x ∈ signedBoxSet S) (hxne : x ≠ 0) :
    ∃ pivot : center,
      x pivot ≠ 0 ∧
        (∀ i : center, |x i| ≤ |x pivot|) ∧
        x ∈ chartMap pivot '' signedBoxSet R := by
  obtain ⟨pivot, hpivot, hmax⟩ := exists_pivot_abs_le_abs_of_ne_zero x hxne
  refine ⟨pivot, hpivot, hmax, ?_⟩
  have hx_pivot : x pivot ∈ Set.Ioo (-(S pivot)) (S pivot) :=
    hxS pivot (Set.mem_univ pivot)
  exact mem_chartMap_image_signedBoxSet_of_pivot_abs_max pivot hpivot
    (lt_of_lt_of_le (abs_lt.mpr hx_pivot) (hSleR pivot)) hmax
    (fun i _hi => hRone i)

/-- Finite selected-entry chart geometry: if all target radii are larger than
`1` and a signed box with radii `S` is contained in the target coordinate box,
then that smaller signed box is covered by the finite family of
selected-entry chart images.

This is only a finite coordinate-cover statement.  It does not identify this
box with an Aoyagi source stratum or construct source-chart data. -/
theorem signedBoxSet_subset_iUnion_chartMap_image_signedBoxSet_of_one_lt
    {center : Finset ι} [Nonempty center] {R S : center → ℝ}
    (hSleR : ∀ i, S i ≤ R i) (hRone : ∀ i, 1 < R i) :
    signedBoxSet S ⊆ ⋃ pivot : center, chartMap pivot '' signedBoxSet R := by
  intro x hxS
  by_cases hxzero : x = 0
  · rcases ‹Nonempty center› with ⟨pivot⟩
    refine Set.mem_iUnion.mpr ⟨pivot, ?_⟩
    rw [mem_chartMap_image_signedBoxSet_iff pivot]
    · exact Or.inl hxzero
    · intro i
      exact zero_lt_one.trans (hRone i)
  · obtain ⟨pivot, _hpivot, _hmax, hmem⟩ :=
      exists_maxPivot_mem_chartMap_image_signedBoxSet_of_mem_signedBoxSet_ne_zero
        hSleR hRone hxS hxzero
    exact Set.mem_iUnion.mpr ⟨pivot, hmem⟩

omit [DecidableEq ι] in
/-- Center-indexed signed boxes are measurable. -/
theorem measurableSet_signedBoxSet {center : Finset ι} (R : center → ℝ) :
    MeasurableSet (signedBoxSet R) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

omit [DecidableEq ι] in
/-- The product of one-dimensional restricted Lebesgue measures on a signed
box is Lebesgue measure restricted to the signed box in finite product
coordinates. -/
theorem signedBoxMeasure_eq_volume_restrict {center : Finset ι}
    (R : center → ℝ) :
    Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i))) =
      (volume : Measure (center → ℝ)).restrict (signedBoxSet R) := by
  rw [volume_pi]
  exact (Measure.restrict_pi_pi
    (μ := fun _ : center => (volume : Measure ℝ))
    (s := fun i : center => Set.Ioo (-(R i)) (R i))).symm

omit [DecidableEq ι] in
/-- The nonzero-pivot locus is measurable in center-indexed coordinates. -/
theorem measurableSet_pivot_ne_zero {center : Finset ι} (pivot : center) :
    MeasurableSet {y : center → ℝ | y pivot ≠ 0} := by
  simpa only [Set.mem_setOf_eq] using
    (((continuous_apply pivot : Continuous fun y : center → ℝ => y pivot).measurable
      (measurableSet_singleton (0 : ℝ))).compl)

omit [DecidableEq ι] in
/-- A signed box with the pivot hyperplane removed is measurable. -/
theorem measurableSet_signedBoxSet_inter_pivot_ne_zero {center : Finset ι}
    (pivot : center) (R : center → ℝ) :
    MeasurableSet (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0}) :=
  (measurableSet_signedBoxSet R).inter (measurableSet_pivot_ne_zero pivot)

omit [DecidableEq ι] in
/-- A signed box with the pivot hyperplane retained is measurable after
intersecting with that hyperplane. -/
theorem measurableSet_signedBoxSet_inter_pivot_eq_zero {center : Finset ι}
    (pivot : center) (R : center → ℝ) :
    MeasurableSet (signedBoxSet R ∩ {y : center → ℝ | y pivot = 0}) := by
  refine (measurableSet_signedBoxSet R).inter ?_
  simpa [Set.compl_setOf] using (measurableSet_pivot_ne_zero pivot).compl

omit [DecidableEq ι] in
/-- The coordinate hyperplane where the selected pivot vanishes has zero
Lebesgue measure in finite center-indexed coordinates. -/
theorem volume_pivot_hyperplane_eq_zero {center : Finset ι} (pivot : center) :
    (volume : Measure (center → ℝ)) {y : center → ℝ | y pivot = 0} = 0 := by
  simpa [volume_pi] using
    (Measure.pi_hyperplane (fun _ : center => (volume : Measure ℝ)) pivot (0 : ℝ))

omit [DecidableEq ι] in
/-- Removing the pivot hyperplane from a signed box does not change it up to
Lebesgue-a.e. equality. -/
theorem signedBoxSet_ae_eq_inter_pivot_ne_zero {center : Finset ι}
    (pivot : center) (R : center → ℝ) :
    (signedBoxSet R : Set (center → ℝ)) =ᶠ[ae (volume : Measure (center → ℝ))]
      ((signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0}) : Set (center → ℝ)) := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · apply measure_mono_null ?_ (volume_pivot_hyperplane_eq_zero pivot)
    intro y hy
    rcases hy with ⟨hybox, hynon⟩
    rw [Set.mem_setOf_eq]
    by_contra hne
    exact hynon ⟨hybox, hne⟩
  · have hsub :
        (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0}) \ signedBoxSet R ⊆
          (∅ : Set (center → ℝ)) := by
      intro y hy
      exact False.elim (hy.2 hy.1.1)
    exact measure_mono_null hsub (by simp)

/-- Off the pivot-zero locus, the center-indexed selected-entry chart map is
injective. -/
theorem injOn_chartMap_pivot_ne_zero {center : Finset ι} (pivot : center) :
    Set.InjOn (chartMap pivot) {y : center → ℝ | y pivot ≠ 0} := by
  intro y hy z _hz h
  funext i
  by_cases hi : i = pivot
  · subst i
    simpa using congr_fun h pivot
  · have hpivot : y pivot = z pivot := by
      simpa using congr_fun h pivot
    have hi_eq : y pivot * y i = z pivot * z i := by
      simpa [chartMap_of_ne pivot y hi, chartMap_of_ne pivot z hi] using congr_fun h i
    rw [← hpivot] at hi_eq
    exact mul_left_cancel₀ hy hi_eq

/-- Fréchet derivative of the center-indexed selected-entry chart map at `y`.
The pivot row is `d ↦ d_p`; each non-pivot row is
`d ↦ y_i d_p + y_p d_i`. -/
def chartMapFDeriv {center : Finset ι} (pivot : center)
    (y : center → ℝ) : (center → ℝ) →L[ℝ] (center → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    if i = pivot then
      ContinuousLinearMap.proj i
    else
      (y i) • (ContinuousLinearMap.proj pivot) +
        (y pivot) • (ContinuousLinearMap.proj i)

@[simp] theorem chartMapFDeriv_apply_pivot {center : Finset ι}
    (pivot : center) (y d : center → ℝ) :
    chartMapFDeriv pivot y d pivot = d pivot := by
  simp [chartMapFDeriv]

theorem chartMapFDeriv_apply_of_ne {center : Finset ι}
    (pivot : center) (y d : center → ℝ) {i : center} (hi : i ≠ pivot) :
    chartMapFDeriv pivot y d i = y i * d pivot + y pivot * d i := by
  simp [chartMapFDeriv, hi]

/-- The actual center-indexed selected-entry chart has the expected
coordinatewise Fréchet derivative. -/
theorem hasFDerivAt_chartMap {center : Finset ι} (pivot : center)
    (y : center → ℝ) :
    HasFDerivAt (chartMap pivot) (chartMapFDeriv pivot y) y := by
  rw [hasFDerivAt_pi']
  intro i
  by_cases hi : i = pivot
  · subst i
    simpa [chartMap, chartMapFDeriv] using
      (hasFDerivAt_apply (𝕜 := ℝ) pivot y)
  · have hfun :
        (fun x : center → ℝ => chartMap pivot x i) =
          fun x : center → ℝ => x pivot * x i := by
      funext x
      exact chartMap_of_ne pivot x hi
    have hpivot :
        HasFDerivAt (fun x : center → ℝ => x pivot)
          (ContinuousLinearMap.proj pivot : (center → ℝ) →L[ℝ] ℝ) y :=
      hasFDerivAt_apply (𝕜 := ℝ) pivot y
    have hi' :
        HasFDerivAt (fun x : center → ℝ => x i)
          (ContinuousLinearMap.proj i : (center → ℝ) →L[ℝ] ℝ) y :=
      hasFDerivAt_apply (𝕜 := ℝ) i y
    rw [hfun]
    convert hpivot.mul hi' using 1
    ext d
    simp [chartMapFDeriv, hi, add_comm]

/-- Within any source set, the selected-entry chart has the same derivative as
in the ambient finite coordinate space. -/
theorem hasFDerivWithinAt_chartMap {center : Finset ι} (pivot : center)
    (y : center → ℝ) (s : Set (center → ℝ)) :
    HasFDerivWithinAt (chartMap pivot) (chartMapFDeriv pivot y) s y :=
  (hasFDerivAt_chartMap pivot y).hasFDerivWithinAt

/-- The determinant of the actual center-indexed derivative of the
selected-entry chart is the selected pivot coordinate raised to the number of
non-pivot center coordinates. -/
theorem chartMapFDeriv_det {center : Finset ι} (pivot : center)
    (y : center → ℝ) :
    (chartMapFDeriv pivot y).det =
      (y pivot) ^ (center.erase pivot.1).card := by
  classical
  let f : (center → ℝ) →ₗ[ℝ] center → ℝ :=
    (chartMapFDeriv pivot y : (center → ℝ) →L[ℝ] center → ℝ)
  let A : Matrix center center ℝ := LinearMap.toMatrix' f
  let D : Matrix center center ℝ :=
    Matrix.diagonal fun i => if i = pivot then 1 else y pivot
  let c : center → ℝ := fun i => if i = pivot then 0 else y i
  have hAD : A.det = D.det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_const c pivot ?_ ?_
    · simp [c]
    · intro i j
      dsimp [A]
      dsimp [D, c, f]
      by_cases hi : i = pivot
      · subst i
        by_cases hj : j = pivot
        · subst j
          simp [chartMapFDeriv]
        · have hpj : pivot ≠ j := by
            intro h
            exact hj h.symm
          simp [chartMapFDeriv, hpj]
      · by_cases hj : j = pivot
        · subst j
          simp [chartMapFDeriv, hi]
        · have hpi : pivot ≠ i := by
            intro h
            exact hi h.symm
          have hpj : pivot ≠ j := by
            intro h
            exact hj h.symm
          by_cases hij : i = j
          · subst j
            simp [chartMapFDeriv, hi, hpi]
          · simp [chartMapFDeriv, hi, hpj, hij]
  have hD : D.det = (y pivot) ^ (center.erase pivot.1).card := by
    rw [Matrix.det_diagonal]
    rw [Fintype.prod_eq_mul_prod_subtype_ne
      (fun i : center => if i = pivot then (1 : ℝ) else y pivot) pivot]
    simp only [ite_true, one_mul]
    have hterm :
        (fun i : {i : center // i ≠ pivot} =>
            if (i : center) = pivot then (1 : ℝ) else y pivot) =
          fun _ => y pivot := by
      funext i
      simp [i.2]
    rw [hterm]
    change (Finset.univ : Finset {i : center // i ≠ pivot}).prod (fun _ => y pivot) =
      y pivot ^ (center.erase pivot.1).card
    rw [Finset.prod_const, Finset.card_univ]
    simp [Finset.card_erase_of_mem pivot.2]
  have hdet : A.det = (chartMapFDeriv pivot y).det := by
    simp [A, f]
  rw [← hdet, hAD, hD]

/-- The center-indexed selected-entry residual square-sum. -/
def residual {center : Finset ι} (pivot : center)
    (y : center → ℝ) : ℝ :=
  selectedEntryCenterSq center
    (selectedEntryChartMap pivot.1 (y pivot) (sourceResidual y))

/-- The center-indexed selected-entry residual is exactly the square-sum of
the selected-entry chart coordinates. -/
theorem residual_eq_aoyagiCoordinateSquareSum_chartMap {center : Finset ι}
    (pivot : center) (y : center → ℝ) :
    residual pivot y =
      aoyagiCoordinateSquareSum (chartMap pivot y) := by
  rw [residual, selectedEntryCenterSq, aoyagiCoordinateSquareSum]
  rw [← Finset.sum_attach center
    (fun i : ι => selectedEntryChartMap pivot.1 (y pivot) (sourceResidual y) i ^ 2)]
  rfl

/-- If another finite coordinate family reads the selected-entry chart
coordinates up to a finite reindexing, its square-sum is the selected-entry
residual. -/
theorem aoyagiCoordinateSquareSum_eq_residual_of_coord_readout
    {η : Type*} [Fintype η] {center : Finset ι} (pivot : center)
    (F : (center → ℝ) → η → ℝ) (e : η ≃ center)
    (hF : ∀ y c, F (chartMap pivot y) c = chartMap pivot y (e c)) :
    ∀ y : center → ℝ,
      aoyagiCoordinateSquareSum (F (chartMap pivot y)) = residual pivot y := by
  intro y
  have hpoint :
      F (chartMap pivot y) = fun c : η => chartMap pivot y (e c) := by
    funext c
    exact hF y c
  calc
    aoyagiCoordinateSquareSum (F (chartMap pivot y)) =
        aoyagiCoordinateSquareSum (fun c : η => chartMap pivot y (e c)) := by
      rw [hpoint]
    _ = aoyagiCoordinateSquareSum (chartMap pivot y) :=
      aoyagiCoordinateSquareSum_comp_equiv e (chartMap pivot y)
    _ = residual pivot y :=
      (residual_eq_aoyagiCoordinateSquareSum_chartMap pivot y).symm

/-- The center-indexed selected-entry residual unit. -/
def residualUnit {center : Finset ι} (pivot : center)
    (y : center → ℝ) : ℝ :=
  selectedEntryCenterSqUnitFactor (center.erase pivot.1)
    (sourceResidual y)

/-- The center-indexed selected-entry formal density unit. -/
def densityUnit {center : Finset ι} (_pivot : center)
    (_y : center → ℝ) : ℝ :=
  1

/-- The center-indexed formal absolute pivot-first determinant density. -/
def sourceDensity {center : Finset ι} (pivot : center)
    (y : center → ℝ) : ℝ :=
  |y pivot| ^ ((center.erase pivot.1).card : ℝ)

/-- The center-indexed selected-entry source density is the absolute value of
the formal pivot-first determinant. -/
theorem sourceDensity_eq_abs_pivotFirstJacobian_det {center : Finset ι}
    (pivot : center) (y : center → ℝ) :
    sourceDensity pivot y =
      |(selectedEntryPivotFirstJacobian
        (κ := {i // i ∈ center.erase pivot.1}) (y pivot)
        (fun p ↦ sourceResidual y p.1)).det| := by
  rw [selectedEntryPivotFirstJacobian_det]
  simp [sourceDensity, Real.rpow_natCast, abs_pow]

/-- The center-indexed selected-entry source density is the absolute
determinant of the actual derivative of the center-indexed chart map. -/
theorem sourceDensity_eq_abs_chartMapFDeriv_det {center : Finset ι}
    (pivot : center) (y : center → ℝ) :
    sourceDensity pivot y = |(chartMapFDeriv pivot y).det| := by
  rw [chartMapFDeriv_det]
  simp [sourceDensity, Real.rpow_natCast, abs_pow]

/-- On any null-measurable set contained in the nonzero-pivot locus, the
center-indexed selected-entry chart pushes forward the weighted source measure
with density `sourceDensity` to Lebesgue measure restricted to the image. -/
theorem map_chartMap_restrict_withDensity_sourceDensity_eq_restrict_image_of_subset_pivot_ne_zero
    {center : Finset ι} (pivot : center) {s : Set (center → ℝ)}
    (hs : NullMeasurableSet s (volume : Measure (center → ℝ)))
    (hsp : s ⊆ {y : center → ℝ | y pivot ≠ 0}) :
    Measure.map (chartMap pivot)
      (((volume : Measure (center → ℝ)).restrict s).withDensity
        (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))) =
      (volume : Measure (center → ℝ)).restrict (chartMap pivot '' s) := by
  rw [show (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y)) =
      fun y : center → ℝ => ENNReal.ofReal |(chartMapFDeriv pivot y).det| from by
        funext y
        rw [sourceDensity_eq_abs_chartMapFDeriv_det]]
  exact MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    (μ := (volume : Measure (center → ℝ))) hs
    (fun y _hy => hasFDerivWithinAt_chartMap pivot y s)
    ((injOn_chartMap_pivot_ne_zero pivot).mono hsp)

/-- On a signed box with the pivot hyperplane removed, the center-indexed
selected-entry chart pushes forward the weighted source measure with density
`sourceDensity` to Lebesgue measure restricted to the image. -/
theorem map_chartMap_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_restrict_image
    {center : Finset ι} (pivot : center) (R : center → ℝ) :
    Measure.map (chartMap pivot)
      (((volume : Measure (center → ℝ)).restrict
          (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0})).withDensity
        (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))) =
      (volume : Measure (center → ℝ)).restrict
        (chartMap pivot '' (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0})) := by
  refine map_chartMap_restrict_withDensity_sourceDensity_eq_restrict_image_of_subset_pivot_ne_zero
    pivot ?_ ?_
  · exact (measurableSet_signedBoxSet_inter_pivot_ne_zero pivot R).nullMeasurableSet
  · exact Set.inter_subset_right

/-- The image of a signed box with the pivot hyperplane removed is measurable
under the center-indexed selected-entry chart. -/
theorem measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero
    {center : Finset ι} (pivot : center) (R : center → ℝ) :
    MeasurableSet
      (chartMap pivot '' (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0})) := by
  exact MeasureTheory.measurable_image_of_fderivWithin
    (measurableSet_signedBoxSet_inter_pivot_ne_zero pivot R)
    (fun y _hy => hasFDerivWithinAt_chartMap pivot y _)
    ((injOn_chartMap_pivot_ne_zero pivot).mono Set.inter_subset_right)

/-- The image of the pivot hyperplane inside a signed box is subsingleton
under the center-indexed selected-entry chart. -/
theorem chartMap_image_signedBoxSet_inter_pivot_eq_zero_subsingleton
    {center : Finset ι} (pivot : center) (R : center → ℝ) :
    (chartMap pivot '' (signedBoxSet R ∩ {y : center → ℝ | y pivot = 0})).Subsingleton := by
  rintro x ⟨y, hy, rfl⟩ z ⟨z, hz, rfl⟩
  rw [chartMap_eq_zero_of_pivot_eq_zero pivot y hy.2]
  rw [chartMap_eq_zero_of_pivot_eq_zero pivot z hz.2]

/-- The image of a signed box under the center-indexed selected-entry chart is
measurable. -/
theorem measurableSet_chartMap_image_signedBoxSet {center : Finset ι}
    (pivot : center) (R : center → ℝ) :
    MeasurableSet (chartMap pivot '' signedBoxSet R) := by
  have hnonzero :
      MeasurableSet
        (chartMap pivot '' (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0})) :=
    measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero pivot R
  have hzero :
      MeasurableSet
        (chartMap pivot '' (signedBoxSet R ∩ {y : center → ℝ | y pivot = 0})) :=
    (chartMap_image_signedBoxSet_inter_pivot_eq_zero_subsingleton pivot R).measurableSet
  have hsplit :
      signedBoxSet R =
        (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0}) ∪
          (signedBoxSet R ∩ {y : center → ℝ | y pivot = 0}) := by
    ext y
    by_cases hy : y pivot = 0 <;> simp [hy]
  rw [hsplit, Set.image_union]
  exact hnonzero.union hzero

/-- A concrete open product box inside the nonzero horn of the selected-entry
chart image. -/
def chartMapTargetInnerBox {center : Finset ι} (pivot : center)
    (R : center → ℝ) : Set (center → ℝ) :=
  Set.univ.pi fun i : center =>
    if i = pivot then
      Set.Ioo (R pivot / 2) (R pivot)
    else
      Set.Ioo (-(R pivot * R i / 4)) (R pivot * R i / 4)

/-- The concrete inner target box is open. -/
theorem isOpen_chartMapTargetInnerBox {center : Finset ι} (pivot : center)
    (R : center → ℝ) :
    IsOpen (chartMapTargetInnerBox pivot R) := by
  rw [chartMapTargetInnerBox]
  refine isOpen_set_pi Set.finite_univ ?_
  intro i _hi
  by_cases hi : i = pivot
  · simpa [hi] using
      (isOpen_Ioo : IsOpen (Set.Ioo (R pivot / 2) (R pivot)))
  · simpa [hi] using
      (isOpen_Ioo :
        IsOpen (Set.Ioo (-(R pivot * R i / 4)) (R pivot * R i / 4)))

/-- Positive radii make the concrete inner target box nonempty. -/
theorem chartMapTargetInnerBox_nonempty {center : Finset ι} (pivot : center)
    {R : center → ℝ} (hR : ∀ i, 0 < R i) :
    (chartMapTargetInnerBox pivot R).Nonempty := by
  rw [chartMapTargetInnerBox, Set.univ_pi_nonempty_iff]
  intro i
  by_cases hi : i = pivot
  · have hlt : R pivot / 2 < R pivot := by linarith [hR pivot]
    simpa [hi] using (Set.nonempty_Ioo.2 hlt)
  · have hlt : -(R pivot * R i / 4) < R pivot * R i / 4 := by
      have hmul : 0 < R pivot * R i := mul_pos (hR pivot) (hR i)
      linarith
    simpa [hi] using (Set.nonempty_Ioo.2 hlt)

/-- The concrete inner target box lies in the selected-entry signed-box chart
image. -/
theorem chartMapTargetInnerBox_subset_chartMap_image_signedBoxSet
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    chartMapTargetInnerBox pivot R ⊆ chartMap pivot '' signedBoxSet R := by
  intro x hx
  rw [mem_chartMap_image_signedBoxSet_iff pivot hR]
  right
  have hxp : x pivot ∈ Set.Ioo (R pivot / 2) (R pivot) := by
    simpa [chartMapTargetInnerBox] using hx pivot (Set.mem_univ pivot)
  have hxp_pos : 0 < x pivot := by
    linarith [hR pivot, hxp.1]
  refine ⟨ne_of_gt hxp_pos, ?_, ?_⟩
  · simpa [abs_of_pos hxp_pos] using hxp.2
  · intro i hi
    have hxi :
        x i ∈ Set.Ioo (-(R pivot * R i / 4)) (R pivot * R i / 4) := by
      simpa [chartMapTargetInnerBox, hi] using hx i (Set.mem_univ i)
    have hxi_abs : |x i| < R pivot * R i / 4 := abs_lt.mpr hxi
    rw [abs_div, abs_of_pos hxp_pos, div_lt_iff₀ hxp_pos]
    have hquarter :
        R pivot * R i / 4 < R i * (R pivot / 2) := by
      have hmul : 0 < R pivot * R i := mul_pos (hR pivot) (hR i)
      nlinarith
    have hhalf : R i * (R pivot / 2) < R i * x pivot :=
      mul_lt_mul_of_pos_left hxp.1 (hR i)
    linarith [hxi_abs, hquarter, hhalf]

/-- The selected-entry signed-box chart image has nonzero Lebesgue measure
when all source radii are positive. -/
theorem volume_chartMap_image_signedBoxSet_ne_zero
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    (volume : Measure (center → ℝ)) (chartMap pivot '' signedBoxSet R) ≠ 0 := by
  have hinner_ne :
      (volume : Measure (center → ℝ)) (chartMapTargetInnerBox pivot R) ≠ 0 :=
    (isOpen_chartMapTargetInnerBox pivot R).measure_ne_zero
      (volume : Measure (center → ℝ))
      (chartMapTargetInnerBox_nonempty pivot hR)
  intro hzero
  exact hinner_ne
    (measure_mono_null
      (chartMapTargetInnerBox_subset_chartMap_image_signedBoxSet pivot hR) hzero)

/-- The Lebesgue measure restricted to the selected-entry signed-box chart
image is nonzero when all source radii are positive. -/
theorem volume_restrict_chartMap_image_signedBoxSet_ne_zero
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    (volume : Measure (center → ℝ)).restrict
      (chartMap pivot '' signedBoxSet R) ≠ 0 := by
  intro hzero
  exact volume_chartMap_image_signedBoxSet_ne_zero pivot hR
    (Measure.restrict_eq_zero.mp hzero)

/-- The image of a signed box under the center-indexed selected-entry chart is
unchanged up to Lebesgue-a.e. equality after removing the pivot hyperplane from
the source. -/
theorem chartMap_image_signedBoxSet_ae_eq_inter_pivot_ne_zero {center : Finset ι}
    (pivot : center) (R : center → ℝ) :
    (chartMap pivot '' signedBoxSet R : Set (center → ℝ)) =ᶠ[ae (volume : Measure (center → ℝ))]
      (chartMap pivot '' (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0}) :
        Set (center → ℝ)) := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · apply measure_mono_null ?_ (volume_pivot_hyperplane_eq_zero pivot)
    intro x hx
    rcases hx with ⟨hximage, hxnonimage⟩
    rcases hximage with ⟨y, hybox, rfl⟩
    rw [Set.mem_setOf_eq]
    by_cases hyp : y pivot = 0
    · simp [chartMap_pivot, hyp]
    · exact False.elim (hxnonimage ⟨y, ⟨hybox, hyp⟩, rfl⟩)
  · have hsub :
        chartMap pivot '' (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0}) \
            chartMap pivot '' signedBoxSet R ⊆
          (∅ : Set (center → ℝ)) := by
      intro x hx
      rcases hx.1 with ⟨y, hy, rfl⟩
      exact False.elim (hx.2 ⟨y, hy.1, rfl⟩)
    exact measure_mono_null hsub (by simp)

/-- Removing the pivot-zero source hyperplane leaves a chart image with
nonzero Lebesgue measure when all source radii are positive. -/
theorem volume_chartMap_image_signedBoxSet_inter_pivot_ne_zero_ne_zero
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    (volume : Measure (center → ℝ))
      (chartMap pivot '' (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0})) ≠ 0 := by
  have hfull := volume_chartMap_image_signedBoxSet_ne_zero pivot hR
  intro hzero
  exact hfull
    ((measure_congr (chartMap_image_signedBoxSet_ae_eq_inter_pivot_ne_zero pivot R)).trans
      hzero)

/-- The Lebesgue measure restricted to the nonzero-pivot signed-box chart
image is nonzero when all source radii are positive. -/
theorem volume_restrict_chartMap_image_signedBoxSet_inter_pivot_ne_zero_ne_zero
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    (volume : Measure (center → ℝ)).restrict
      (chartMap pivot '' (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0})) ≠ 0 := by
  intro hzero
  exact volume_chartMap_image_signedBoxSet_inter_pivot_ne_zero_ne_zero pivot hR
    (Measure.restrict_eq_zero.mp hzero)

/-- The center-indexed selected-entry chart pushes forward the weighted
signed-box source measure with density `sourceDensity` to Lebesgue measure
restricted to the signed-box chart image. -/
theorem map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
    {center : Finset ι} (pivot : center) (R : center → ℝ) :
    Measure.map (chartMap pivot)
      ((Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
        (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))) =
      (volume : Measure (center → ℝ)).restrict (chartMap pivot '' signedBoxSet R) := by
  rw [signedBoxMeasure_eq_volume_restrict R]
  have hsource :
      (volume : Measure (center → ℝ)).restrict (signedBoxSet R) =
        (volume : Measure (center → ℝ)).restrict
          (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0}) :=
    Measure.restrict_congr_set (signedBoxSet_ae_eq_inter_pivot_ne_zero pivot R)
  rw [hsource]
  calc
    Measure.map (chartMap pivot)
        (((volume : Measure (center → ℝ)).restrict
            (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0})).withDensity
          (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y)))
        = (volume : Measure (center → ℝ)).restrict
            (chartMap pivot '' (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0})) := by
          exact
            map_chartMap_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_restrict_image
              pivot R
    _ = (volume : Measure (center → ℝ)).restrict (chartMap pivot '' signedBoxSet R) := by
          exact Measure.restrict_congr_set
            (chartMap_image_signedBoxSet_ae_eq_inter_pivot_ne_zero pivot R).symm

/-- The weighted selected-entry signed-box source measure is nonzero when all
source radii are positive. -/
theorem signedBoxMeasure_withDensity_sourceDensity_ne_zero
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    ((Measure.pi
      (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))).withDensity
      (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))) ≠ 0 := by
  intro hzero
  have htarget := volume_restrict_chartMap_image_signedBoxSet_ne_zero pivot hR
  have hmap :=
    map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
      pivot R
  rw [hzero, Measure.map_zero] at hmap
  exact htarget hmap.symm

/-- The weighted selected-entry source measure on the nonzero-pivot signed
box is nonzero when all source radii are positive. -/
theorem restrict_nonzeroSignedBox_withDensity_sourceDensity_ne_zero
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    (((volume : Measure (center → ℝ)).restrict
        (signedBoxSet R ∩ {y : center → ℝ | y pivot ≠ 0})).withDensity
      (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))) ≠ 0 := by
  intro hzero
  have htarget :=
    volume_restrict_chartMap_image_signedBoxSet_inter_pivot_ne_zero_ne_zero pivot hR
  have hmap :=
    map_chartMap_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_restrict_image
      pivot R
  rw [hzero, Measure.map_zero] at hmap
  exact htarget hmap.symm

/-- Center-indexed loss exponents: only the selected pivot has exponent `1`. -/
def lossExp {center : Finset ι} (pivot : center) (i : center) : ℕ :=
  if i = pivot then 1 else 0

/-- Center-indexed formal density exponents: only the selected pivot carries
the formal determinant exponent. -/
def densityExp {center : Finset ι} (pivot : center) (i : center) : ℕ :=
  if i = pivot then (center.erase pivot.1).card else 0

/-- Pointwise center-indexed selected-entry loss monomial-unit identity. -/
theorem residual_eq_unit_mul_abs_monomial {center : Finset ι} (pivot : center)
    (y : center → ℝ) :
    residual pivot y =
      residualUnit pivot y * ∏ i : center, |y i| ^ (2 * (lossExp pivot i : ℝ)) := by
  rw [residual, selectedEntryCenterSq_selectedEntryChartMap pivot.2]
  simp [residualUnit, selectedEntryCenterSqUnitFactor, lossExp,
    pow_two, mul_comm, mul_assoc]

/-- Pointwise center-indexed selected-entry formal-density monomial-unit
identity. -/
theorem sourceDensity_eq_unit_mul_abs_monomial {center : Finset ι}
    (pivot : center) (y : center → ℝ) :
    sourceDensity pivot y =
      densityUnit pivot y * ∏ i : center, |y i| ^ (densityExp pivot i : ℝ) := by
  simp [sourceDensity, densityUnit, densityExp]

/-- A center-indexed selected-entry residual is bounded above when all center
coordinates are uniformly small. -/
theorem residual_le_sq_of_abs_le {center : Finset ι} (pivot : center)
    {y : center → ℝ} {δ R : ℝ}
    (hδ : 0 ≤ δ) (hyδ : ∀ i : center, |y i| ≤ δ)
    (hsmall :
      δ ^ 2 * (1 + ((center.erase pivot.1).card : ℝ) * δ ^ 2) ≤ R ^ 2) :
    residual pivot y ≤ R ^ 2 := by
  have hpivot_sq : y pivot ^ 2 ≤ δ ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hδ] using hyδ pivot)
  have hsum_le :
      selectedEntryCenterSq (center.erase pivot.1) (sourceResidual y) ≤
        ((center.erase pivot.1).card : ℝ) * δ ^ 2 := by
    rw [selectedEntryCenterSq]
    calc
      ∑ i ∈ center.erase pivot.1, sourceResidual y i ^ 2 ≤
          ∑ _i ∈ center.erase pivot.1, δ ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hicenter : i ∈ center := (Finset.mem_erase.mp hi).2
        have hcoord : |sourceResidual y i| ≤ δ := by
          simpa [sourceResidual, hicenter] using hyδ ⟨i, hicenter⟩
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hδ] using hcoord)
      _ = ((center.erase pivot.1).card : ℝ) * δ ^ 2 := by
        simp
  have hunit_le :
      1 + selectedEntryCenterSq (center.erase pivot.1) (sourceResidual y) ≤
        1 + ((center.erase pivot.1).card : ℝ) * δ ^ 2 := by
    linarith
  have hunit_nonneg :
      0 ≤ 1 + selectedEntryCenterSq (center.erase pivot.1) (sourceResidual y) := by
    exact add_nonneg zero_le_one
      (selectedEntryCenterSq_nonneg (center.erase pivot.1) (sourceResidual y))
  calc
    residual pivot y =
        y pivot ^ 2 *
          (1 + selectedEntryCenterSq (center.erase pivot.1) (sourceResidual y)) := by
      rw [residual, selectedEntryCenterSq_selectedEntryChartMap pivot.2]
    _ ≤ δ ^ 2 * (1 + ((center.erase pivot.1).card : ℝ) * δ ^ 2) := by
      exact mul_le_mul hpivot_sq hunit_le hunit_nonneg (sq_nonneg δ)
    _ ≤ R ^ 2 := hsmall

/-- A center-indexed selected-entry residual is bounded above on a signed box
whose radii are uniformly small enough. -/
theorem residual_le_sq_of_mem_signedBoxSet {center : Finset ι} (pivot : center)
    {y : center → ℝ} {Rres : center → ℝ} {δ R : ℝ}
    (hδ : 0 ≤ δ) (hRres_le : ∀ i : center, Rres i ≤ δ)
    (hsmall :
      δ ^ 2 * (1 + ((center.erase pivot.1).card : ℝ) * δ ^ 2) ≤ R ^ 2)
    (hy : y ∈ signedBoxSet Rres) :
    residual pivot y ≤ R ^ 2 := by
  refine residual_le_sq_of_abs_le pivot hδ ?_ hsmall
  intro i
  have hi : y i ∈ Set.Ioo (-(Rres i)) (Rres i) := hy i (Set.mem_univ i)
  exact (le_of_lt (abs_lt.mpr hi)).trans (hRres_le i)

/-- The center-indexed selected-entry residual is bounded a.e. on a sufficiently
small signed box. -/
theorem residual_le_sq_ae_signedBox_of_smallBox {center : Finset ι} (pivot : center)
    {Rres : center → ℝ} {δ R : ℝ}
    (hδ : 0 ≤ δ) (hRres_le : ∀ i : center, Rres i ≤ δ)
    (hsmall :
      δ ^ 2 * (1 + ((center.erase pivot.1).card : ℝ) * δ ^ 2) ≤ R ^ 2) :
    ∀ᵐ y : center → ℝ
      ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      residual pivot y ≤ R ^ 2 := by
  let signedBox : Measure (center → ℝ) :=
    Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
  have hmem : ∀ᵐ y : center → ℝ ∂ signedBox, y ∈ signedBoxSet Rres := by
    change ∀ᵐ y : center → ℝ
      ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      y ∈ signedBoxSet Rres
    rw [signedBoxMeasure_eq_volume_restrict Rres]
    exact ae_restrict_mem (measurableSet_signedBoxSet Rres)
  filter_upwards [hmem] with y hy
  exact residual_le_sq_of_mem_signedBoxSet pivot hδ hRres_le hsmall hy

/-- The center-indexed selected-entry residual is bounded a.e. for the weighted
signed-box source measure when the signed-box radii are sufficiently small. -/
theorem residual_le_sq_ae_withDensity_sourceDensity_of_smallBox
    {center : Finset ι} (pivot : center)
    {Rres : center → ℝ} {δ R : ℝ}
    (hδ : 0 ≤ δ) (hRres_le : ∀ i : center, Rres i ≤ δ)
    (hsmall :
      δ ^ 2 * (1 + ((center.erase pivot.1).card : ℝ) * δ ^ 2) ≤ R ^ 2) :
    ∀ᵐ y : center → ℝ
      ∂(Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
        (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y)),
      residual pivot y ≤ R ^ 2 := by
  let signedBox : Measure (center → ℝ) :=
    Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
  exact
    (withDensity_absolutelyContinuous signedBox
      (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))).ae_le
      (residual_le_sq_ae_signedBox_of_smallBox
        (pivot := pivot) (Rres := Rres) (δ := δ) (R := R)
        hδ hRres_le hsmall)

/-- The center-indexed selected-entry residual unit is bounded below by `1`. -/
theorem one_le_residualUnit {center : Finset ι} (pivot : center)
    (y : center → ℝ) :
    1 ≤ residualUnit pivot y := by
  rw [residualUnit, selectedEntryCenterSqUnitFactor]
  exact le_add_of_nonneg_right
    (selectedEntryCenterSq_nonneg (center.erase pivot.1) (sourceResidual y))

omit [DecidableEq ι] in
/-- The center-indexed selected-entry formal density unit is nonnegative. -/
theorem densityUnit_nonneg {center : Finset ι} (pivot : center)
    (y : center → ℝ) :
    0 ≤ densityUnit pivot y := by
  simp [densityUnit]

omit [DecidableEq ι] in
/-- The center-indexed selected-entry formal density unit is bounded above by
`1`. -/
theorem densityUnit_le_one {center : Finset ι} (pivot : center)
    (y : center → ℝ) :
    densityUnit pivot y ≤ 1 := by
  simp [densityUnit]

omit [DecidableEq ι] in
/-- The center-indexed selected-entry formal density unit is a.e. measurable
on any signed box with this coordinate index. -/
theorem densityUnit_aemeasurable {center : Finset ι} (pivot : center)
    (R : center → ℝ) :
    AEMeasurable (densityUnit pivot)
      (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))) := by
  exact aemeasurable_const

/-- Center-indexed selected-entry pointwise monomial-unit identities and unit
bounds, packaged as a.e. hypotheses over an arbitrary signed box. -/
theorem monomialUnitHypotheses {center : Finset ι} (pivot : center)
    (R : center → ℝ) :
    AEMeasurable (densityUnit pivot)
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))) ∧
      (∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i))),
        residual pivot y =
          residualUnit pivot y * ∏ i, |y i| ^ (2 * (lossExp pivot i : ℝ))) ∧
      (∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i))),
        sourceDensity pivot y =
          densityUnit pivot y * ∏ i, |y i| ^ (densityExp pivot i : ℝ)) ∧
      (∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i))),
        1 ≤ residualUnit pivot y) ∧
      (∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i))),
        0 ≤ densityUnit pivot y) ∧
      (∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i))),
        densityUnit pivot y ≤ 1) := by
  refine ⟨densityUnit_aemeasurable pivot R, ?_, ?_, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun y => residual_eq_unit_mul_abs_monomial pivot y
  · exact Filter.Eventually.of_forall fun y => sourceDensity_eq_unit_mul_abs_monomial pivot y
  · exact Filter.Eventually.of_forall fun y => one_le_residualUnit pivot y
  · exact Filter.Eventually.of_forall fun y => densityUnit_nonneg pivot y
  · exact Filter.Eventually.of_forall fun y => densityUnit_le_one pivot y

/-- The center-indexed selected-entry monomial-unit package specialized
through the existing signed-box inequality consumer, with constants
`c = C = 1`. -/
theorem monomialLower_sourceDensityBounds {center : Finset ι} (pivot : center)
    (R : center → ℝ) :
    AEMeasurable (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))
        (Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))) ∧
      (∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i))),
        1 * ∏ i, |y i| ^ (2 * (lossExp pivot i : ℝ)) ≤ residual pivot y) ∧
      (∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i))),
        0 ≤ sourceDensity pivot y) ∧
      (∀ᵐ y : center → ℝ
        ∂Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i))),
        sourceDensity pivot y ≤ 1 * ∏ i, |y i| ^ (densityExp pivot i : ℝ)) := by
  rcases monomialUnitHypotheses pivot R with
    ⟨hdensityUnit_aemeas, hres_eq, hsourceDensity_eq, hresUnit_lower,
      hdensityUnit_nonneg, hdensityUnit_le⟩
  exact
    signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
      (residual := residual pivot)
      (sourceDensity := sourceDensity pivot)
      (residualUnit := residualUnit pivot)
      (densityUnit := densityUnit pivot)
      (R := R) (h := densityExp pivot) (k := lossExp pivot) (c := 1) (C := 1)
      hdensityUnit_aemeas hres_eq hsourceDensity_eq hresUnit_lower
      hdensityUnit_nonneg hdensityUnit_le

set_option linter.style.longLine false in
/-- Selected-entry weighted signed-box residual positivity and finite
negative-power integral.

This proves the actual selected-entry model field under the formal
pivot-Jacobian source density.  It does not identify any retained-passive or
original DLN source measure with this weighted signed-box measure. -/
theorem residual_pos_ae_and_lintegral_rpow_neg_withDensity_sourceDensity
    {center : Finset ι} (pivot : center) {t : ℝ} {R : center → ℝ}
    (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : 2 * t < ((center.erase pivot.1).card : ℝ) + 1) :
    let signedBox : Measure (center → ℝ) :=
      Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))
    let weightedBox : Measure (center → ℝ) :=
      signedBox.withDensity
        (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))
    (∀ᵐ y ∂ weightedBox, 0 < residual pivot y) ∧
      (∫⁻ y : center → ℝ,
        ENNReal.ofReal ((residual pivot y) ^ (-t)) ∂ weightedBox) < ∞ := by
  let signedBox : Measure (center → ℝ) :=
    Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))
  let weightedBox : Measure (center → ℝ) :=
    signedBox.withDensity
      (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))
  rcases monomialLower_sourceDensityBounds pivot R with
    ⟨hsourceDensity_aemeas, hres_lower, hsourceDensity_nonneg, hsourceDensity_le⟩
  have hcrit_all :
      ∀ i : center,
        2 * t * (lossExp pivot i : ℝ) <
          (densityExp pivot i : ℝ) + 1 := by
    intro i
    by_cases hi : i = pivot
    · subst i
      simpa [lossExp, densityExp, mul_assoc] using hcrit
    · simp [lossExp, densityExp, hi]
  have hpos_signed :
      ∀ᵐ y ∂ signedBox, 0 < residual pivot y := by
    have hcoord :
        ∀ᵐ y : center → ℝ ∂ signedBox, ∀ i, 0 < |y i| := by
      dsimp [signedBox]
      exact ae_forall_abs_pos_measure_pi_restrict_Ioo_neg (R := R) (ι := center)
    filter_upwards [hcoord, hres_lower] with y hyabs hylower
    have hmonomial_pos :
        0 < ∏ i, |y i| ^ (2 * (lossExp pivot i : ℝ)) := by
      exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hyabs i) _
    exact lt_of_lt_of_le (by simpa using hmonomial_pos) hylower
  have hpos_weighted :
      ∀ᵐ y ∂ weightedBox, 0 < residual pivot y := by
    exact
      (withDensity_absolutelyContinuous signedBox
        (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))).ae_le
        hpos_signed
  have hfinite_signed :
      (∫⁻ y : center → ℝ,
        ENNReal.ofReal ((residual pivot y) ^ (-t) * sourceDensity pivot y)
          ∂ signedBox) < ∞ := by
    dsimp [signedBox]
    exact
      lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top
        (h := densityExp pivot) (k := lossExp pivot) (t := t) (R := R)
        (c := 1) (C := 1) (loss := residual pivot)
        (density := sourceDensity pivot)
        (by norm_num) (by norm_num) ht hR hcrit_all hres_lower
        hsourceDensity_nonneg hsourceDensity_le
  have hfinite_weighted :
      (∫⁻ y : center → ℝ,
        ENNReal.ofReal ((residual pivot y) ^ (-t)) ∂ weightedBox) < ∞ := by
    have hdensity_lt_top :
        ∀ᵐ y : center → ℝ ∂ signedBox,
          ENNReal.ofReal (sourceDensity pivot y) < ∞ := by
      filter_upwards with y
      exact ENNReal.ofReal_lt_top
    have hwith :
        (∫⁻ y : center → ℝ,
          ENNReal.ofReal ((residual pivot y) ^ (-t)) ∂ weightedBox) =
            ∫⁻ y : center → ℝ,
              ENNReal.ofReal (sourceDensity pivot y) *
                ENNReal.ofReal ((residual pivot y) ^ (-t)) ∂ signedBox := by
      dsimp [weightedBox]
      rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀
        signedBox (by simpa [signedBox] using hsourceDensity_aemeas)
        hdensity_lt_top
        (fun y : center → ℝ => ENNReal.ofReal ((residual pivot y) ^ (-t)))]
      simp [Pi.mul_apply]
    have hmul :
        (∫⁻ y : center → ℝ,
          ENNReal.ofReal (sourceDensity pivot y) *
            ENNReal.ofReal ((residual pivot y) ^ (-t)) ∂ signedBox) =
            ∫⁻ y : center → ℝ,
              ENNReal.ofReal ((residual pivot y) ^ (-t) * sourceDensity pivot y)
                ∂ signedBox := by
      apply lintegral_congr_ae
      filter_upwards [hsourceDensity_nonneg] with y hyden_nonneg
      rw [mul_comm]
      exact (ENNReal.ofReal_mul' hyden_nonneg).symm
    calc
      (∫⁻ y : center → ℝ,
        ENNReal.ofReal ((residual pivot y) ^ (-t)) ∂ weightedBox)
          = ∫⁻ y : center → ℝ,
              ENNReal.ofReal (sourceDensity pivot y) *
                ENNReal.ofReal ((residual pivot y) ^ (-t)) ∂ signedBox := hwith
      _ = ∫⁻ y : center → ℝ,
            ENNReal.ofReal ((residual pivot y) ^ (-t) * sourceDensity pivot y)
              ∂ signedBox := hmul
      _ < ∞ := hfinite_signed
  exact ⟨hpos_weighted, hfinite_weighted⟩

set_option linter.style.longLine false in
/-- Selected-entry chart-image residual positivity and finite negative-power
integral.

This pushes the selected-entry weighted source-box theorem through the
center-indexed selected-entry chart map.  It is still only a finite
selected-entry target-image statement, not a retained-passive source
production theorem. -/
theorem aoyagiCoordinateSquareSum_pos_ae_and_lintegral_rpow_neg_restrict_chartMap_image
    {center : Finset ι} (pivot : center) {t : ℝ} {R : center → ℝ}
    (ht : 0 ≤ t) (hR : ∀ i, 0 < R i)
    (hcrit : 2 * t < ((center.erase pivot.1).card : ℝ) + 1) :
    (∀ᵐ x ∂ (volume : Measure (center → ℝ)).restrict
        (chartMap pivot '' signedBoxSet R),
        0 < aoyagiCoordinateSquareSum x) ∧
      (∫⁻ x : center → ℝ,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum x) ^ (-t))
          ∂ (volume : Measure (center → ℝ)).restrict
              (chartMap pivot '' signedBoxSet R)) < ∞ := by
  let signedBox : Measure (center → ℝ) :=
    Measure.pi (fun i : center => volume.restrict (Set.Ioo (-(R i)) (R i)))
  let weightedBox : Measure (center → ℝ) :=
    signedBox.withDensity
      (fun y : center → ℝ => ENNReal.ofReal (sourceDensity pivot y))
  have hmap :
      Measure.map (chartMap pivot) weightedBox =
        (volume : Measure (center → ℝ)).restrict
          (chartMap pivot '' signedBoxSet R) := by
    dsimp [weightedBox, signedBox]
    exact map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
      pivot R
  rcases
      residual_pos_ae_and_lintegral_rpow_neg_withDensity_sourceDensity
        pivot ht hR hcrit with
    ⟨hpos_source, hfinite_source⟩
  change (∀ᵐ y ∂ weightedBox, 0 < residual pivot y) at hpos_source
  change
    (∫⁻ y : center → ℝ,
      ENNReal.ofReal ((residual pivot y) ^ (-t)) ∂ weightedBox) < ∞
    at hfinite_source
  have hpos_meas :
      MeasurableSet {x : center → ℝ | 0 < aoyagiCoordinateSquareSum x} := by
    have hsquare :
        Measurable (fun x : center → ℝ => aoyagiCoordinateSquareSum x) :=
      measurable_aoyagiCoordinateSquareSum measurable_id
    simpa [Set.preimage] using hsquare measurableSet_Ioi
  have hpos_chart :
      ∀ᵐ y ∂ weightedBox,
        0 < aoyagiCoordinateSquareSum (chartMap pivot y) := by
    filter_upwards [hpos_source] with y hy
    simpa [residual_eq_aoyagiCoordinateSquareSum_chartMap pivot y] using hy
  have hpos_target :
      ∀ᵐ x ∂ (volume : Measure (center → ℝ)).restrict
          (chartMap pivot '' signedBoxSet R),
        0 < aoyagiCoordinateSquareSum x := by
    have hpos_map :
        ∀ᵐ x ∂ Measure.map (chartMap pivot) weightedBox,
          0 < aoyagiCoordinateSquareSum x :=
      (ae_map_iff (measurable_chartMap pivot).aemeasurable hpos_meas).2 hpos_chart
    simpa [hmap] using hpos_map
  have hfinite_chart :
      (∫⁻ y : center → ℝ,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (chartMap pivot y)) ^ (-t))
          ∂ weightedBox) < ∞ := by
    refine lt_of_eq_of_lt ?_ hfinite_source
    apply lintegral_congr_ae
    filter_upwards with y
    rw [← residual_eq_aoyagiCoordinateSquareSum_chartMap pivot y]
  have hfinite_target :
      (∫⁻ x : center → ℝ,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum x) ^ (-t))
          ∂ (volume : Measure (center → ℝ)).restrict
              (chartMap pivot '' signedBoxSet R)) < ∞ := by
    have hle :
        (∫⁻ x : center → ℝ,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum x) ^ (-t))
            ∂ Measure.map (chartMap pivot) weightedBox) ≤
          ∫⁻ y : center → ℝ,
            ENNReal.ofReal
              ((aoyagiCoordinateSquareSum (chartMap pivot y)) ^ (-t))
              ∂ weightedBox := by
      exact
        lintegral_map_le
          (fun x : center → ℝ =>
            ENNReal.ofReal ((aoyagiCoordinateSquareSum x) ^ (-t)))
          (chartMap pivot)
    exact lt_of_le_of_lt (by simpa [hmap] using hle) hfinite_chart
  exact ⟨hpos_target, hfinite_target⟩

end CenterCoord

end SelectedEntrySignedBox

end Aoyagi
end DLN
end DLNFibre
