import DLNFibre.DLN.Aoyagi.SelectedEntryOneChartAnalyticPredicateData

/-!
# One-chart selected-entry source-coverage obstruction

This file records the elementary obstruction to treating the single
selected-entry chart with `sourceDomain = Set.univ` as source-covering.

If the finite center has a non-pivot coordinate, then the vector with pivot
coordinate `0` and that non-pivot coordinate `1` belongs to the universal
source domain but not to the image of the one selected-entry chart.  This is
because the chart map has the form `(u, r) |-> (x_p = u, x_i = u * r_i)`, so
the whole pivot-zero fibre maps to the origin.

This does not rule out source coverage for a different source domain, a
multi-pivot atlas, or a separately supplied analytic atlas.  It does not
construct source production, branch termination, normal-crossing extraction,
pole order, or an RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace SelectedEntrySignedBox
namespace CenterCoord

variable {ι : Type*} [DecidableEq ι]

/-- The selected-entry chart-point map sends the pivot coordinate to the
chart-point first coordinate. -/
theorem formalChartMap_pivot
    {center : Finset ι} (pivot : center) (x : FormalChartPoint pivot) :
    formalChartMap pivot x pivot = x.1 := by
  rw [formalChartMap_eq_selectedEntryChartMap]
  simp [selectedEntryChartMap]

/-- If the chart-point first coordinate is zero, the one-chart selected-entry
map collapses to the origin. -/
theorem formalChartMap_eq_zero_of_fst_eq_zero
    {center : Finset ι} (pivot : center) (x : FormalChartPoint pivot)
    (hx : x.1 = 0) :
    formalChartMap pivot x = 0 := by
  funext i
  rw [formalChartMap_eq_selectedEntryChartMap]
  simp [selectedEntryChartMap, hx]

/-- The one-chart selected-entry context with universal source domain cannot
provide source coverage when the center has a non-pivot coordinate.

This obstruction is only for `selectedEntryOneChartAnalyticAtlasContext pivot`.
It does not say that another source domain, a multi-pivot atlas, or a supplied
analytic atlas cannot cover its source domain. -/
theorem not_selectedEntryOneChartAnalyticSourceCoverageData_of_ne
    {center : Finset ι} (pivot q : center) (hq : q ≠ pivot) :
    ¬ SelectedEntryAnalyticSourceCoverageData
      (selectedEntryOneChartAnalyticAtlasContext pivot) := by
  intro hcov
  let value : center → ℝ := fun i => if i = q then 1 else 0
  have hmem : value ∈ (selectedEntryOneChartAnalyticAtlasContext pivot).sourceDomain := by
    trivial
  have hcover := hcov.sourceDomain_subset_chart_images hmem
  rw [Set.mem_iUnion] at hcover
  rcases hcover with ⟨c, hc⟩
  rw [Set.mem_image] at hc
  rcases hc with ⟨y, _hyDomain, hyEq⟩
  fin_cases c
  change formalChartMap pivot y = value at hyEq
  have hpivot_ne_q : pivot ≠ q := fun h => hq h.symm
  have hy_first_zero : y.1 = 0 := by
    have hp := congrFun hyEq pivot
    rw [formalChartMap_pivot pivot y] at hp
    have hvalue_pivot : value pivot = 0 := by
      simp [value, hpivot_ne_q]
    exact hp.trans hvalue_pivot
  have hmap_zero : formalChartMap pivot y = 0 :=
    formalChartMap_eq_zero_of_fst_eq_zero pivot y hy_first_zero
  have hvalue_zero : value = 0 := by
    rw [← hyEq]
    exact hmap_zero
  have hq_zero := congrFun hvalue_zero q
  norm_num [value] at hq_zero

end CenterCoord
end SelectedEntrySignedBox

end Aoyagi
end DLN
end DLNFibre
