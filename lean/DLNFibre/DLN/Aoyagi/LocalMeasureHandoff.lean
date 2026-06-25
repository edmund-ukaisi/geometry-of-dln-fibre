import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.NhdsWithin

/-!
# Local filter facts as restricted-measure a.e. facts

This file records a small measure-theoretic handoff used by local chart
arguments: a property that holds eventually in a relative neighborhood holds
almost everywhere after restricting any measure to a sufficiently small
measurable source neighborhood.

It does not construct Aoyagi's p. 13 product chart, compare losses, transport
density, or prove any integrability theorem.
-/

noncomputable section

open MeasureTheory

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- A property holding eventually in `nhdsWithin x₀ s` holds a.e. after
restricting any measure to a sufficiently small open neighborhood intersected
with `s`. -/
theorem exists_open_ae_restrict_inter_of_eventually_nhdsWithin
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α} {x₀ : α} {s : Set α} (hs : MeasurableSet s)
    {p : α → Prop}
    (hp : ∀ᶠ x in nhdsWithin x₀ s, p x) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ x ∂ μ.restrict (U ∩ s), p x := by
  rcases mem_nhdsWithin.1 hp with ⟨U, hUopen, hxU, hsub⟩
  exact
    ⟨U, hUopen, hxU,
      ae_restrict_of_forall_mem (hUopen.measurableSet.inter hs)
        (fun x hx => hsub hx)⟩

/-- Product-measure version of
`exists_open_ae_restrict_inter_of_eventually_nhdsWithin`: after the same base
restriction, a relative-neighborhood property of the first coordinate holds
a.e. for the product measure. -/
theorem exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {x₀ : α} {s : Set α}
    (hs : MeasurableSet s) {p : α → Prop}
    (hp : ∀ᶠ x in nhdsWithin x₀ s, p x) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ z : α × β ∂ (μ.restrict (U ∩ s)).prod ν, p z.1 := by
  rcases exists_open_ae_restrict_inter_of_eventually_nhdsWithin
      (μ := μ) (x₀ := x₀) hs hp with
    ⟨U, hUopen, hxU, hpU⟩
  exact
    ⟨U, hUopen, hxU,
      (Measure.quasiMeasurePreserving_fst
        (μ := μ.restrict (U ∩ s)) (ν := ν)).ae hpU⟩

end Aoyagi
end DLN
end DLNFibre

end
