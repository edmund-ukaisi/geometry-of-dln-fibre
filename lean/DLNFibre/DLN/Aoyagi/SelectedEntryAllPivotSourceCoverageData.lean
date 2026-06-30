import DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasProducer

/-!
# All-pivot selected-entry source coverage data

This file packages the finite all-pivot selected-entry chart-family coverage
theorem as `SelectedEntryAnalyticSourceCoverageData` for a shared context with
universal source and chart domains.

It does not prove chart regularity, transition regularity, unit regularity,
Jacobian/volume compatibility, source production, branch termination,
normal-crossing extraction, pole order, or RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

variable {ι : Type*} [DecidableEq ι]

/-- Shared universal-domain context for the all-pivot selected-entry finite
chart family.

This only supplies the domains needed for source coverage.  It is not a full
analytic atlas producer. -/
def selectedEntryAllPivotAnalyticAtlasContext
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    SelectedEntryAnalyticAtlasContext
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := ℝ) hcenter chartEquiv) where
  chartTopology := fun c ↦ by
    change TopologicalSpace
      (ℝ × ((center.erase (chartEquiv c).1 : Finset ι) → ℝ))
    infer_instance
  sourceDomain := Set.univ
  chartDomain := fun _ ↦ Set.univ
  sourceDomain_isOpen := isOpen_univ
  chartDomain_isOpen := by
    intro c
    change @IsOpen
      (ℝ × ((center.erase (chartEquiv c).1 : Finset ι) → ℝ))
      inferInstance Set.univ
    exact isOpen_univ
  sourceDomain_nonempty := ⟨0, trivial⟩

/-- The all-pivot selected-entry chart family covers the universal finite
center source domain.

This is the finite coordinate coverage field only; it does not supply any
other analytic atlas data. -/
def selectedEntryAllPivotAnalyticSourceCoverageData
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    SelectedEntryAnalyticSourceCoverageData
      (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv) where
  sourceDomain_subset_chart_images := by
    intro value _hvalue
    rcases
      selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value
        (K := ℝ) hcenter chartEquiv value with
      ⟨c, x, hx⟩
    rw [Set.mem_iUnion]
    refine ⟨c, ?_⟩
    exact ⟨x, trivial, hx⟩

/-- Forgetful predicate wrapper for all-pivot selected-entry source coverage.

This wraps only `SelectedEntryAnalyticSourceCoverageData`; it is not a supplied
analytic atlas producer. -/
theorem selectedEntryAllPivotAnalyticSourceCoverage
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    SelectedEntryAnalyticSourceCoverage
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := ℝ) hcenter chartEquiv) := by
  exact ⟨selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv,
    ⟨selectedEntryAllPivotAnalyticSourceCoverageData hcenter chartEquiv⟩⟩

end Aoyagi
end DLN
end DLNFibre
