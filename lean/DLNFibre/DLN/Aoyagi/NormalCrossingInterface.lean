import DLNFibre.DLN.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod

/-!
# Finite normal-crossing exponent interface for Aoyagi's RLCT citation

This file records only the finite exponent arithmetic in Aoyagi's
normal-crossing extraction formula.  It does not prove the analytic
resolution theorem, construct charts, identify an RLCT, prove ideal-generator
invariance, prove regular-coordinate additivity, or prove a deepest-point
comparison.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Finite exponent data from a supplied normal-crossing chart family.

The analytic chart certificate, nonvanishing unit factors, and prior
hypotheses are outside this data structure; they enter through the explicit
extraction hypothesis below. -/
structure AoyagiNormalCrossingExponentData where
  numCharts : ℕ
  numCoords : ℕ
  lossExp : Fin numCharts → Fin numCoords → ℕ
  jacobianPriorExp : Fin numCharts → Fin numCoords → ℕ
  active_nonempty :
    ∃ p : Fin numCharts × Fin numCoords, 0 < lossExp p.1 p.2

namespace AoyagiNormalCrossingExponentData

/-- Coordinates with positive loss exponent `k_j`; zero-exponent coordinates
are ignored in Aoyagi's finite minimum. -/
def activePairs (D : AoyagiNormalCrossingExponentData) :
    Finset (Fin D.numCharts × Fin D.numCoords) :=
  (Finset.univ : Finset (Fin D.numCharts × Fin D.numCoords)).filter
    fun p ↦ 0 < D.lossExp p.1 p.2

@[simp] theorem mem_activePairs (D : AoyagiNormalCrossingExponentData)
    (p : Fin D.numCharts × Fin D.numCoords) :
    p ∈ D.activePairs ↔ 0 < D.lossExp p.1 p.2 := by
  simp [activePairs]

/-- The active coordinate set is nonempty by hypothesis. -/
theorem activePairs_nonempty (D : AoyagiNormalCrossingExponentData) :
    D.activePairs.Nonempty := by
  rcases D.active_nonempty with ⟨p, hp⟩
  exact ⟨p, by simpa using hp⟩

/-- Aoyagi's finite ratio `(h_j+1)/(2 k_j)` for a chart coordinate.

This function is total, but it should be minimized only over `activePairs`,
where `k_j > 0`. -/
def ratioAt (D : AoyagiNormalCrossingExponentData)
    (p : Fin D.numCharts × Fin D.numCoords) : ℚ :=
  ((D.jacobianPriorExp p.1 p.2 + 1 : ℕ) : ℚ) /
    (2 * (D.lossExp p.1 p.2 : ℚ))

/-- The finite set of ratios attached to active chart coordinates. -/
def activeRatios (D : AoyagiNormalCrossingExponentData) : Finset ℚ :=
  D.activePairs.image fun p ↦ D.ratioAt p

/-- The active ratio set is nonempty. -/
theorem activeRatios_nonempty (D : AoyagiNormalCrossingExponentData) :
    D.activeRatios.Nonempty :=
  D.activePairs_nonempty.image _

/-- The finite minimum in Aoyagi's normal-crossing exponent formula. -/
def exponentMinimum (D : AoyagiNormalCrossingExponentData) : ℚ :=
  D.activeRatios.min' D.activeRatios_nonempty

/-- The exponent minimum is one of the active ratios. -/
theorem exponentMinimum_mem_activeRatios (D : AoyagiNormalCrossingExponentData) :
    D.exponentMinimum ∈ D.activeRatios := by
  simpa [exponentMinimum] using D.activeRatios.min'_mem D.activeRatios_nonempty

/-- The exponent minimum is bounded above by every active-coordinate ratio. -/
theorem exponentMinimum_le_ratioAt_of_mem_activePairs
    (D : AoyagiNormalCrossingExponentData)
    {p : Fin D.numCharts × Fin D.numCoords} (hp : p ∈ D.activePairs) :
    D.exponentMinimum ≤ D.ratioAt p := by
  exact D.activeRatios.min'_le (D.ratioAt p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- Some active chart coordinate realizes the exponent minimum. -/
theorem exists_activePair_ratioAt_eq_exponentMinimum
    (D : AoyagiNormalCrossingExponentData) :
    ∃ p ∈ D.activePairs, D.ratioAt p = D.exponentMinimum := by
  have hmem := D.exponentMinimum_mem_activeRatios
  rw [activeRatios] at hmem
  rcases Finset.mem_image.mp hmem with ⟨p, hp, hratio⟩
  exact ⟨p, hp, hratio⟩

/-- Certify the finite exponent minimum by exhibiting a candidate active ratio
which lower-bounds all active ratios. -/
theorem exponentMinimum_eq_of_mem_activeRatios_of_forall_le
    (D : AoyagiNormalCrossingExponentData) {q : ℚ}
    (hmem : q ∈ D.activeRatios)
    (hle : ∀ r ∈ D.activeRatios, q ≤ r) :
    D.exponentMinimum = q := by
  apply le_antisymm
  · exact D.activeRatios.min'_le q hmem
  · exact hle D.exponentMinimum D.exponentMinimum_mem_activeRatios

/-- Certify the finite exponent minimum from an active coordinate realizing
the candidate value and a lower bound against all active coordinates. -/
theorem exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
    (D : AoyagiNormalCrossingExponentData)
    {p : Fin D.numCharts × Fin D.numCoords} {q : ℚ}
    (hp : p ∈ D.activePairs)
    (hratio : D.ratioAt p = q)
    (hle : ∀ p' ∈ D.activePairs, q ≤ D.ratioAt p') :
    D.exponentMinimum = q := by
  refine D.exponentMinimum_eq_of_mem_activeRatios_of_forall_le ?_ ?_
  · exact Finset.mem_image.mpr ⟨p, hp, hratio⟩
  · intro r hr
    rw [activeRatios] at hr
    rcases Finset.mem_image.mp hr with ⟨p', hp', rfl⟩
    exact hle p' hp'

/-- Coordinates in one chart attaining the global exponent minimum. -/
def minCoordsInChart (D : AoyagiNormalCrossingExponentData)
    (c : Fin D.numCharts) : Finset (Fin D.numCoords) :=
  (Finset.univ : Finset (Fin D.numCoords)).filter
    fun j ↦ 0 < D.lossExp c j ∧ D.ratioAt (c, j) = D.exponentMinimum

/-- Coordinates in one chart with positive loss exponent and a specified
ratio.  This is a source-facing variant of `minCoordsInChart`; it becomes the
minimum-coordinate set after the specified ratio is proved to be
`D.exponentMinimum`. -/
def coordsInChartAtRatio (D : AoyagiNormalCrossingExponentData)
    (q : ℚ) (c : Fin D.numCharts) : Finset (Fin D.numCoords) :=
  (Finset.univ : Finset (Fin D.numCoords)).filter
    fun j ↦ 0 < D.lossExp c j ∧ D.ratioAt (c, j) = q

@[simp] theorem mem_minCoordsInChart
    (D : AoyagiNormalCrossingExponentData) (c : Fin D.numCharts)
    (j : Fin D.numCoords) :
    j ∈ D.minCoordsInChart c ↔
      0 < D.lossExp c j ∧ D.ratioAt (c, j) = D.exponentMinimum := by
  simp [minCoordsInChart]

@[simp] theorem mem_coordsInChartAtRatio
    (D : AoyagiNormalCrossingExponentData) (q : ℚ)
    (c : Fin D.numCharts) (j : Fin D.numCoords) :
    j ∈ D.coordsInChartAtRatio q c ↔
      0 < D.lossExp c j ∧ D.ratioAt (c, j) = q := by
  simp [coordsInChartAtRatio]

/-- The chartwise count used before taking the maximum finite order count. -/
def minCountInChart (D : AoyagiNormalCrossingExponentData)
    (c : Fin D.numCharts) : ℕ :=
  (D.minCoordsInChart c).card

/-- The chartwise count of coordinates at a specified active ratio. -/
def countInChartAtRatio (D : AoyagiNormalCrossingExponentData)
    (q : ℚ) (c : Fin D.numCharts) : ℕ :=
  (D.coordsInChartAtRatio q c).card

/-- Once a candidate ratio is identified with the global exponent minimum,
the source-facing ratio-specific coordinate set is the minimum-coordinate
set. -/
theorem minCoordsInChart_eq_coordsInChartAtRatio_of_exponentMinimum_eq
    (D : AoyagiNormalCrossingExponentData) {q : ℚ}
    (hmin : D.exponentMinimum = q) (c : Fin D.numCharts) :
    D.minCoordsInChart c = D.coordsInChartAtRatio q c := by
  ext j
  simp [hmin]

/-- Count form of
`minCoordsInChart_eq_coordsInChartAtRatio_of_exponentMinimum_eq`. -/
theorem minCountInChart_eq_countInChartAtRatio_of_exponentMinimum_eq
    (D : AoyagiNormalCrossingExponentData) {q : ℚ}
    (hmin : D.exponentMinimum = q) (c : Fin D.numCharts) :
    D.minCountInChart c = D.countInChartAtRatio q c := by
  rw [minCountInChart, countInChartAtRatio,
    D.minCoordsInChart_eq_coordsInChartAtRatio_of_exponentMinimum_eq hmin c]

/-- The chart index set is nonempty because an active coordinate exists. -/
theorem chart_univ_nonempty (D : AoyagiNormalCrossingExponentData) :
    (Finset.univ : Finset (Fin D.numCharts)).Nonempty := by
  rcases D.active_nonempty with ⟨p, _hp⟩
  exact ⟨p.1, Finset.mem_univ _⟩

/-- The set of chartwise global-minimum counts. -/
def chartMinCounts (D : AoyagiNormalCrossingExponentData) : Finset ℕ :=
  (Finset.univ : Finset (Fin D.numCharts)).image fun c ↦ D.minCountInChart c

/-- The chartwise-count set is nonempty. -/
theorem chartMinCounts_nonempty (D : AoyagiNormalCrossingExponentData) :
    D.chartMinCounts.Nonempty :=
  D.chart_univ_nonempty.image _

/-- The finite order count appearing in Aoyagi's exponent formula: maximum
chartwise number of coordinates attaining the global exponent minimum. -/
def exponentOrder (D : AoyagiNormalCrossingExponentData) : ℕ :=
  D.chartMinCounts.max' D.chartMinCounts_nonempty

/-- Every chartwise global-minimum count is bounded by the exponent order. -/
theorem minCountInChart_le_exponentOrder
    (D : AoyagiNormalCrossingExponentData) (c : Fin D.numCharts) :
    D.minCountInChart c ≤ D.exponentOrder := by
  exact D.chartMinCounts.le_max' (D.minCountInChart c)
    (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)

/-- Some chart realizes the exponent order. -/
theorem exists_chart_minCount_eq_exponentOrder
    (D : AoyagiNormalCrossingExponentData) :
    ∃ c : Fin D.numCharts, D.minCountInChart c = D.exponentOrder := by
  have hmem : D.exponentOrder ∈ D.chartMinCounts := by
    simpa [exponentOrder] using D.chartMinCounts.max'_mem D.chartMinCounts_nonempty
  rw [chartMinCounts] at hmem
  rcases Finset.mem_image.mp hmem with ⟨c, _hc, hcount⟩
  exact ⟨c, hcount⟩

/-- Certify the finite exponent order by exhibiting a candidate chart count
which upper-bounds all chart counts. -/
theorem exponentOrder_eq_of_mem_chartMinCounts_of_forall_le
    (D : AoyagiNormalCrossingExponentData) {q : ℕ}
    (hmem : q ∈ D.chartMinCounts)
    (hle : ∀ r ∈ D.chartMinCounts, r ≤ q) :
    D.exponentOrder = q := by
  apply le_antisymm
  · exact hle D.exponentOrder
      (by simpa [exponentOrder] using
        D.chartMinCounts.max'_mem D.chartMinCounts_nonempty)
  · exact D.chartMinCounts.le_max' q hmem

/-- Certify the finite exponent order from one chart realizing the candidate
count and a uniform upper bound for all chart counts. -/
theorem exponentOrder_eq_of_chart_minCount_eq_of_forall_le
    (D : AoyagiNormalCrossingExponentData)
    {c : Fin D.numCharts} {q : ℕ}
    (hchart : D.minCountInChart c = q)
    (hle : ∀ c' : Fin D.numCharts, D.minCountInChart c' ≤ q) :
    D.exponentOrder = q := by
  refine D.exponentOrder_eq_of_mem_chartMinCounts_of_forall_le ?_ ?_
  · exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hchart⟩
  · intro r hr
    rw [chartMinCounts] at hr
    rcases Finset.mem_image.mp hr with ⟨c', _hc', rfl⟩
    exact hle c'

/-- Certify the finite exponent order using chart counts at a candidate ratio,
after that ratio has been identified with the global exponent minimum. -/
theorem exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
    (D : AoyagiNormalCrossingExponentData)
    {ratio : ℚ} {c : Fin D.numCharts} {q : ℕ}
    (hmin : D.exponentMinimum = ratio)
    (hchart : D.countInChartAtRatio ratio c = q)
    (hle : ∀ c' : Fin D.numCharts, D.countInChartAtRatio ratio c' ≤ q) :
    D.exponentOrder = q := by
  refine D.exponentOrder_eq_of_chart_minCount_eq_of_forall_le (c := c) ?_ ?_
  · rw [D.minCountInChart_eq_countInChartAtRatio_of_exponentMinimum_eq hmin c]
    exact hchart
  · intro c'
    rw [D.minCountInChart_eq_countInChartAtRatio_of_exponentMinimum_eq hmin c']
    exact hle c'

/-- Certify the finite exponent order from a uniform upper bound and an
existence theorem for a chart attaining the candidate count. -/
theorem exponentOrder_eq_of_forall_le_of_exists_chart_minCount_eq
    (D : AoyagiNormalCrossingExponentData) {q : ℕ}
    (hle : ∀ c : Fin D.numCharts, D.minCountInChart c ≤ q)
    (hexists : ∃ c : Fin D.numCharts, D.minCountInChart c = q) :
    D.exponentOrder = q := by
  rcases hexists with ⟨c, hchart⟩
  exact D.exponentOrder_eq_of_chart_minCount_eq_of_forall_le hchart hle

/-- The exponent order is positive because the global minimum is attained by
an active coordinate. -/
theorem one_le_exponentOrder (D : AoyagiNormalCrossingExponentData) :
    1 ≤ D.exponentOrder := by
  rcases D.exists_activePair_ratioAt_eq_exponentMinimum with ⟨p, hp, hratio⟩
  have hmem : p.2 ∈ D.minCoordsInChart p.1 := by
    exact D.mem_minCoordsInChart p.1 p.2 |>.mpr ⟨by simpa using hp, hratio⟩
  have hpos : 0 < D.minCountInChart p.1 := by
    exact Finset.card_pos.mpr ⟨p.2, hmem⟩
  exact le_trans hpos (D.minCountInChart_le_exponentOrder p.1)

end AoyagiNormalCrossingExponentData

/-- Explicit hypothesis supplied by the cited analytic normal-crossing
extraction theorem.

This structure is not a proof of that analytic theorem; it records the
interface that a later final theorem may assume after supplying genuine
normal-crossing chart data. -/
structure AoyagiNormalCrossingExtractionHypothesis
    (D : AoyagiNormalCrossingExponentData) (lambda : ℚ) (theta : ℕ) : Prop where
  lambda_eq_exponentMinimum : lambda = D.exponentMinimum
  theta_eq_exponentOrder : theta = D.exponentOrder

end Aoyagi
end DLN
end DLNFibre
