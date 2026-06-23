import DLNFibre.DLN.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

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

/-- A coordinate with loss exponent `1` is active. -/
theorem mem_activePairs_of_lossExp_eq_one
    (D : AoyagiNormalCrossingExponentData)
    {p : Fin D.numCharts × Fin D.numCoords}
    (hloss : D.lossExp p.1 p.2 = 1) :
    p ∈ D.activePairs :=
  (D.mem_activePairs p).mpr (by simp [hloss])

/-- If a coordinate has loss exponent `1` and supplied numerator `N = h+1`,
then its finite normal-crossing ratio is `N/2`. -/
theorem ratioAt_eq_nat_div_two_of_lossExp_eq_one_of_jacobianPriorExp_add_one_eq
    (D : AoyagiNormalCrossingExponentData)
    {p : Fin D.numCharts × Fin D.numCoords} {N : ℕ}
    (hloss : D.lossExp p.1 p.2 = 1)
    (hjac : D.jacobianPriorExp p.1 p.2 + 1 = N) :
    D.ratioAt p = (N : ℚ) / 2 := by
  rw [ratioAt, hloss, hjac]
  norm_num

/-- Finite operation that adds `m * k_j` to every Jacobian/prior exponent
`h_j`, while leaving the loss exponents `k_j` unchanged.

This is only exponent-array arithmetic. It does not construct new charts,
regular coordinates, normal crossings, or an RLCT additivity theorem. -/
def jacobianPriorLossShift (D : AoyagiNormalCrossingExponentData) (m : ℕ) :
    AoyagiNormalCrossingExponentData where
  numCharts := D.numCharts
  numCoords := D.numCoords
  lossExp := D.lossExp
  jacobianPriorExp := fun c j ↦
    D.jacobianPriorExp c j + m * D.lossExp c j
  active_nonempty := D.active_nonempty

@[simp] theorem jacobianPriorLossShift_lossExp
    (D : AoyagiNormalCrossingExponentData) (m : ℕ)
    (c : Fin D.numCharts) (j : Fin D.numCoords) :
    (D.jacobianPriorLossShift m).lossExp c j = D.lossExp c j := rfl

@[simp] theorem jacobianPriorLossShift_jacobianPriorExp
    (D : AoyagiNormalCrossingExponentData) (m : ℕ)
    (c : Fin D.numCharts) (j : Fin D.numCoords) :
    (D.jacobianPriorLossShift m).jacobianPriorExp c j =
      D.jacobianPriorExp c j + m * D.lossExp c j := rfl

@[simp] theorem activePairs_jacobianPriorLossShift
    (D : AoyagiNormalCrossingExponentData) (m : ℕ) :
    (D.jacobianPriorLossShift m).activePairs = D.activePairs := rfl

@[simp] theorem mem_activePairs_jacobianPriorLossShift
    (D : AoyagiNormalCrossingExponentData) (m : ℕ)
    (p : Fin D.numCharts × Fin D.numCoords) :
    p ∈ (D.jacobianPriorLossShift m).activePairs ↔ p ∈ D.activePairs := by
  rw [activePairs_jacobianPriorLossShift]
  rfl

/-- On active coordinates, adding `m * k_j` to `h_j` shifts the finite
normal-crossing ratio by `m/2`.

The active-coordinate hypothesis is essential because `ratioAt` is totalized
when `k_j = 0`. -/
theorem ratioAt_jacobianPriorLossShift_of_mem_activePairs
    (D : AoyagiNormalCrossingExponentData) (m : ℕ)
    {p : Fin D.numCharts × Fin D.numCoords}
    (hp : p ∈ D.activePairs) :
    (D.jacobianPriorLossShift m).ratioAt p =
      D.ratioAt p + (m : ℚ) / 2 := by
  have hkpos : 0 < D.lossExp p.1 p.2 := (D.mem_activePairs p).mp hp
  have hk : (D.lossExp p.1 p.2 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hkpos)
  rw [ratioAt, ratioAt]
  simp only [jacobianPriorLossShift_jacobianPriorExp, jacobianPriorLossShift_lossExp]
  norm_num [Nat.cast_add, Nat.cast_mul]
  field_simp [hk]
  ring

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

/-- Under a finite Jacobian/prior loss shift, the minimum of the active
normal-crossing ratios shifts by `m/2`. -/
theorem exponentMinimum_jacobianPriorLossShift
    (D : AoyagiNormalCrossingExponentData) (m : ℕ) :
    (D.jacobianPriorLossShift m).exponentMinimum =
      D.exponentMinimum + (m : ℚ) / 2 := by
  rcases D.exists_activePair_ratioAt_eq_exponentMinimum with ⟨p, hp, hratio⟩
  refine (D.jacobianPriorLossShift m).exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
    (p := p) ?_ ?_ ?_
  · rw [D.activePairs_jacobianPriorLossShift m]
    exact hp
  · rw [D.ratioAt_jacobianPriorLossShift_of_mem_activePairs m hp, hratio]
  · intro p' hp'
    have hpD : p' ∈ D.activePairs :=
      (D.mem_activePairs_jacobianPriorLossShift m p').mp hp'
    rw [D.ratioAt_jacobianPriorLossShift_of_mem_activePairs m hpD]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right (D.exponentMinimum_le_ratioAt_of_mem_activePairs hpD)
        ((m : ℚ) / 2)

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

/-- Coordinates at ratio `q` are exactly the shifted-data coordinates at
ratio `q + m/2`. -/
theorem coordsInChartAtRatio_jacobianPriorLossShift
    (D : AoyagiNormalCrossingExponentData) (m : ℕ)
    (q : ℚ) (c : Fin D.numCharts) :
    (D.jacobianPriorLossShift m).coordsInChartAtRatio
      (q + (m : ℚ) / 2) c = D.coordsInChartAtRatio q c := by
  ext j
  constructor
  · intro hj
    rcases ((D.jacobianPriorLossShift m).mem_coordsInChartAtRatio
      (q + (m : ℚ) / 2) c j).mp hj with ⟨hposShift, hratioShift⟩
    have hpos : 0 < D.lossExp c j := by simpa using hposShift
    have hp : (c, j) ∈ D.activePairs := (D.mem_activePairs (c, j)).mpr hpos
    have hshift := D.ratioAt_jacobianPriorLossShift_of_mem_activePairs m hp
    have hadd :
        D.ratioAt (c, j) + (m : ℚ) / 2 =
          q + (m : ℚ) / 2 := by
      exact hshift.symm.trans hratioShift
    exact (D.mem_coordsInChartAtRatio q c j).mpr
      ⟨hpos, add_right_cancel hadd⟩
  · intro hj
    rcases (D.mem_coordsInChartAtRatio q c j).mp hj with ⟨hpos, hratio⟩
    have hp : (c, j) ∈ D.activePairs := (D.mem_activePairs (c, j)).mpr hpos
    have hshift := D.ratioAt_jacobianPriorLossShift_of_mem_activePairs m hp
    exact ((D.jacobianPriorLossShift m).mem_coordsInChartAtRatio
      (q + (m : ℚ) / 2) c j).mpr
      ⟨by simpa using hpos, by
        calc
          (D.jacobianPriorLossShift m).ratioAt (c, j) =
              D.ratioAt (c, j) + (m : ℚ) / 2 := hshift
          _ = q + (m : ℚ) / 2 := by rw [hratio]⟩

/-- The chartwise count used before taking the maximum finite order count. -/
def minCountInChart (D : AoyagiNormalCrossingExponentData)
    (c : Fin D.numCharts) : ℕ :=
  (D.minCoordsInChart c).card

/-- The chartwise count of coordinates at a specified active ratio. -/
def countInChartAtRatio (D : AoyagiNormalCrossingExponentData)
    (q : ℚ) (c : Fin D.numCharts) : ℕ :=
  (D.coordsInChartAtRatio q c).card

/-- Count form of `coordsInChartAtRatio_jacobianPriorLossShift`. -/
theorem countInChartAtRatio_jacobianPriorLossShift
    (D : AoyagiNormalCrossingExponentData) (m : ℕ)
    (q : ℚ) (c : Fin D.numCharts) :
    (D.jacobianPriorLossShift m).countInChartAtRatio
      (q + (m : ℚ) / 2) c = D.countInChartAtRatio q c := by
  rw [countInChartAtRatio, countInChartAtRatio,
    D.coordsInChartAtRatio_jacobianPriorLossShift m q c]
  rfl

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

/-- The coordinates attaining the shifted global minimum are the original
minimum-attaining coordinates. -/
theorem minCoordsInChart_jacobianPriorLossShift
    (D : AoyagiNormalCrossingExponentData) (m : ℕ)
    (c : Fin D.numCharts) :
    (D.jacobianPriorLossShift m).minCoordsInChart c =
      D.minCoordsInChart c := by
  rw [(D.jacobianPriorLossShift m).minCoordsInChart_eq_coordsInChartAtRatio_of_exponentMinimum_eq
    (D.exponentMinimum_jacobianPriorLossShift m) c]
  rw [D.coordsInChartAtRatio_jacobianPriorLossShift m D.exponentMinimum c]
  rw [← D.minCoordsInChart_eq_coordsInChartAtRatio_of_exponentMinimum_eq rfl c]

/-- Chartwise minimum counts are preserved by a finite Jacobian/prior loss
shift. -/
theorem minCountInChart_jacobianPriorLossShift
    (D : AoyagiNormalCrossingExponentData) (m : ℕ)
    (c : Fin D.numCharts) :
    (D.jacobianPriorLossShift m).minCountInChart c =
      D.minCountInChart c := by
  rw [minCountInChart, minCountInChart,
    D.minCoordsInChart_jacobianPriorLossShift m c]
  rfl

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

/-- The finite pole-order count is unchanged by a Jacobian/prior loss shift.

This is a statement about the finite exponent arrays only, not about analytic
regular-coordinate additivity. -/
theorem exponentOrder_jacobianPriorLossShift
    (D : AoyagiNormalCrossingExponentData) (m : ℕ) :
    (D.jacobianPriorLossShift m).exponentOrder = D.exponentOrder := by
  refine (D.jacobianPriorLossShift m).exponentOrder_eq_of_forall_le_of_exists_chart_minCount_eq
    ?_ ?_
  · intro c
    rw [D.minCountInChart_jacobianPriorLossShift m c]
    exact D.minCountInChart_le_exponentOrder c
  · rcases D.exists_chart_minCount_eq_exponentOrder with ⟨c, hcount⟩
    exact ⟨c, by rw [D.minCountInChart_jacobianPriorLossShift m c, hcount]⟩

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

universe u

/-- Source-facing normal-crossing chart certificate.

This records the finite chart domains, chart map, coordinates, monomial
loss/Jacobian-prior identities, unit factors, and exponent arrays from
Aoyagi's normal-crossing display.  It is a certificate *spine*: it does not
state that the charts analytically cover a neighbourhood, that the chart map
is proper or analytic, or that the analytic normal-crossing extraction theorem
applies.  Those remain in the explicit extraction hypothesis below.

Aoyagi prints the unit-free monomial form on PDF pp. 5-6; the unit fields allow
the standard normal-crossing form and specialize to the printed display by
taking both units to be `1`. -/
structure AoyagiNormalCrossingChartCertificate
    (Param R : Type*) [CommMonoid R] where
  numCharts : ℕ
  numCoords : ℕ
  ChartPoint : Fin numCharts → Type u
  chartPoint_nonempty : ∀ c : Fin numCharts, Nonempty (ChartPoint c)
  chartMap : ∀ c : Fin numCharts, ChartPoint c → Param
  coord : ∀ c : Fin numCharts, ChartPoint c → Fin numCoords → R
  loss : Param → R
  jacobianPrior : ∀ c : Fin numCharts, ChartPoint c → R
  lossUnit : ∀ c : Fin numCharts, ChartPoint c → R
  jacobianPriorUnit : ∀ c : Fin numCharts, ChartPoint c → R
  lossExp : Fin numCharts → Fin numCoords → ℕ
  jacobianPriorExp : Fin numCharts → Fin numCoords → ℕ
  loss_monomial :
    ∀ (c : Fin numCharts) (u : ChartPoint c),
      loss (chartMap c u) =
        lossUnit c u * ∏ j : Fin numCoords,
          coord c u j ^ (2 * lossExp c j)
  jacobianPrior_monomial :
    ∀ (c : Fin numCharts) (u : ChartPoint c),
      jacobianPrior c u =
        jacobianPriorUnit c u * ∏ j : Fin numCoords,
          coord c u j ^ jacobianPriorExp c j
  lossUnit_isUnit :
    ∀ (c : Fin numCharts) (u : ChartPoint c), IsUnit (lossUnit c u)
  jacobianPriorUnit_isUnit :
    ∀ (c : Fin numCharts) (u : ChartPoint c), IsUnit (jacobianPriorUnit c u)
  active_nonempty :
    ∃ p : Fin numCharts × Fin numCoords, 0 < lossExp p.1 p.2

namespace AoyagiNormalCrossingChartCertificate

variable {Param R : Type*} [CommMonoid R]

/-- Forget the chart-level functions and units, keeping only the finite
exponent arrays used by the arithmetic normal-crossing interface. -/
def exponentData (C : AoyagiNormalCrossingChartCertificate Param R) :
    AoyagiNormalCrossingExponentData where
  numCharts := C.numCharts
  numCoords := C.numCoords
  lossExp := C.lossExp
  jacobianPriorExp := C.jacobianPriorExp
  active_nonempty := C.active_nonempty

@[simp] theorem exponentData_numCharts
    (C : AoyagiNormalCrossingChartCertificate Param R) :
    C.exponentData.numCharts = C.numCharts := rfl

@[simp] theorem exponentData_numCoords
    (C : AoyagiNormalCrossingChartCertificate Param R) :
    C.exponentData.numCoords = C.numCoords := rfl

@[simp] theorem exponentData_lossExp
    (C : AoyagiNormalCrossingChartCertificate Param R)
    (c : Fin C.numCharts) (j : Fin C.numCoords) :
    C.exponentData.lossExp c j = C.lossExp c j := rfl

@[simp] theorem exponentData_jacobianPriorExp
    (C : AoyagiNormalCrossingChartCertificate Param R)
    (c : Fin C.numCharts) (j : Fin C.numCoords) :
    C.exponentData.jacobianPriorExp c j = C.jacobianPriorExp c j := rfl

@[simp] theorem mem_exponentData_activePairs
    (C : AoyagiNormalCrossingChartCertificate Param R)
    (p : Fin C.numCharts × Fin C.numCoords) :
    p ∈ C.exponentData.activePairs ↔ 0 < C.lossExp p.1 p.2 := by
  change
    p ∈ ((Finset.univ : Finset (Fin C.numCharts × Fin C.numCoords)).filter
      fun p ↦ 0 < C.lossExp p.1 p.2) ↔
    0 < C.lossExp p.1 p.2
  simp

end AoyagiNormalCrossingChartCertificate

/-- Explicit hypothesis supplied by the cited analytic normal-crossing
extraction theorem.

This structure is not a proof of that analytic theorem; it records the
interface that a later final theorem may assume after supplying genuine
normal-crossing chart data. -/
structure AoyagiNormalCrossingExtractionHypothesis
    (D : AoyagiNormalCrossingExponentData) (lambda : ℚ) (theta : ℕ) : Prop where
  lambda_eq_exponentMinimum : lambda = D.exponentMinimum
  theta_eq_exponentOrder : theta = D.exponentOrder

namespace AoyagiNormalCrossingChartCertificate

variable {Param R : Type*} [CommMonoid R]

/-- Chart-level version of the cited extraction hypothesis.

The theorem that turns a genuine analytic chart certificate into this
hypothesis is the single allowed analytic citation. -/
structure ExtractionHypothesis
    (C : AoyagiNormalCrossingChartCertificate Param R)
    (lambda : ℚ) (theta : ℕ) : Prop where
  toExponentData :
    AoyagiNormalCrossingExtractionHypothesis C.exponentData lambda theta

namespace ExtractionHypothesis

/-- The cited chart-level extraction hypothesis identifies the external
learning coefficient with the finite exponent minimum of the certificate. -/
theorem lambda_eq_exponentMinimum
    {C : AoyagiNormalCrossingChartCertificate Param R}
    {lambda : ℚ} {theta : ℕ}
    (H : C.ExtractionHypothesis lambda theta) :
    lambda = C.exponentData.exponentMinimum :=
  H.toExponentData.lambda_eq_exponentMinimum

/-- The cited chart-level extraction hypothesis identifies the external order
with the finite exponent order of the certificate. -/
theorem theta_eq_exponentOrder
    {C : AoyagiNormalCrossingChartCertificate Param R}
    {lambda : ℚ} {theta : ℕ}
    (H : C.ExtractionHypothesis lambda theta) :
    theta = C.exponentData.exponentOrder :=
  H.toExponentData.theta_eq_exponentOrder

end ExtractionHypothesis

end AoyagiNormalCrossingChartCertificate

end Aoyagi
end DLN
end DLNFibre
