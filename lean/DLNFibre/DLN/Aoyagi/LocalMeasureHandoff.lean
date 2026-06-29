import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.NhdsWithin

/-!
# Local filter facts as restricted-measure a.e. facts

This file records a small measure-theoretic handoff used by local chart
arguments: a property that holds eventually in a relative neighborhood holds
almost everywhere after restricting any measure to a sufficiently small
measurable source neighborhood.  It also records the elementary topological
boundedness fact for a supplied positive continuous density factor.

It does not construct Aoyagi's p. 13 product chart, compare losses, transport
Jacobian/density factors, or prove any integrability theorem.
-/

noncomputable section

open MeasureTheory

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- A nonnegative real function is positive almost everywhere once its zero
locus is null. -/
theorem ae_pos_of_forall_nonneg_of_measure_zero_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hnonneg : ∀ x, 0 ≤ f x) (hzero : μ {x | f x = 0} = 0) :
    ∀ᵐ x ∂ μ, 0 < f x := by
  rw [ae_iff]
  exact measure_mono_null (fun x hx ↦ le_antisymm (le_of_not_gt hx) (hnonneg x)) hzero

/-- A positive continuous density factor at `(x₀,0)` is uniformly nonnegative
and bounded on a sufficiently small product neighborhood, with the radius
chosen below any supplied positive cap. -/
theorem exists_pos_radius_le_eventually_density_bounds_of_continuousAt_pos
    {α E : Type*} [TopologicalSpace α] [PseudoMetricSpace E] [Zero E]
    {density : α × E → ℝ} {x₀ : α} {Rmax : ℝ}
    (hdensity : ContinuousAt density (x₀, 0))
    (hpos : 0 < density (x₀, 0)) (hRmax : 0 < Rmax) :
    ∃ R C : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧
      (∀ᶠ x in nhds x₀,
        ∀ u : E, u ∈ Metric.ball (0 : E) R → 0 ≤ density (x, u)) ∧
      (∀ᶠ x in nhds x₀,
        ∀ u : E, u ∈ Metric.ball (0 : E) R → density (x, u) ≤ C) := by
  let C := density (x₀, 0) + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  have htarget : Set.Ioo (0 : ℝ) C ∈ nhds (density (x₀, 0)) := by
    exact isOpen_Ioo.mem_nhds ⟨hpos, by dsimp [C]; linarith⟩
  have hpre : {z : α × E | density z ∈ Set.Ioo (0 : ℝ) C} ∈ nhds (x₀, 0) :=
    hdensity htarget
  rcases mem_nhds_prod_iff.mp hpre with ⟨U, hU, V, hV, hUV⟩
  rcases Metric.mem_nhds_iff.1 hV with ⟨R₀, hR₀, hR₀V⟩
  let R := min R₀ Rmax
  have hR : 0 < R := by
    dsimp [R]
    exact lt_min hR₀ hRmax
  have hR_le_R₀ : R ≤ R₀ := by
    dsimp [R]
    exact min_le_left _ _
  have hR_le_Rmax : R ≤ Rmax := by
    dsimp [R]
    exact min_le_right _ _
  refine ⟨R, C, hR, hR_le_Rmax, hC, ?_, ?_⟩
  · exact Filter.eventually_of_mem hU fun x hx u hu ↦ by
      have huR₀ : u ∈ Metric.ball (0 : E) R₀ :=
        Metric.ball_subset_ball hR_le_R₀ hu
      exact le_of_lt (hUV ⟨hx, hR₀V huR₀⟩).1
  · exact Filter.eventually_of_mem hU fun x hx u hu ↦ by
      have huR₀ : u ∈ Metric.ball (0 : E) R₀ :=
        Metric.ball_subset_ball hR_le_R₀ hu
      exact le_of_lt (hUV ⟨hx, hR₀V huR₀⟩).2

/-- A positive continuous density factor at `(x₀,0)` is uniformly bounded
above and below by a positive lower constant on a sufficiently small product
neighborhood, with the radius chosen below any supplied positive cap. -/
theorem exists_pos_radius_le_eventually_density_two_sided_bounds_of_continuousAt_pos
    {α E : Type*} [TopologicalSpace α] [PseudoMetricSpace E] [Zero E]
    {density : α × E → ℝ} {x₀ : α} {Rmax : ℝ}
    (hdensity : ContinuousAt density (x₀, 0))
    (hpos : 0 < density (x₀, 0)) (hRmax : 0 < Rmax) :
    ∃ R d D : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 < d ∧ 0 ≤ D ∧
      (∀ᶠ x in nhds x₀,
        ∀ u : E, u ∈ Metric.ball (0 : E) R → d ≤ density (x, u)) ∧
      (∀ᶠ x in nhds x₀,
        ∀ u : E, u ∈ Metric.ball (0 : E) R → density (x, u) ≤ D) := by
  let d := density (x₀, 0) / 2
  let D := density (x₀, 0) + 1
  have hd : 0 < d := by
    dsimp [d]
    exact half_pos hpos
  have hD : 0 ≤ D := by
    dsimp [D]
    linarith
  have htarget : Set.Ioo d D ∈ nhds (density (x₀, 0)) := by
    exact isOpen_Ioo.mem_nhds
      ⟨by dsimp [d]; linarith, by dsimp [D]; linarith⟩
  have hpre : {z : α × E | density z ∈ Set.Ioo d D} ∈ nhds (x₀, 0) :=
    hdensity htarget
  rcases mem_nhds_prod_iff.mp hpre with ⟨U, hU, V, hV, hUV⟩
  rcases Metric.mem_nhds_iff.1 hV with ⟨R₀, hR₀, hR₀V⟩
  let R := min R₀ Rmax
  have hR : 0 < R := by
    dsimp [R]
    exact lt_min hR₀ hRmax
  have hR_le_R₀ : R ≤ R₀ := by
    dsimp [R]
    exact min_le_left _ _
  have hR_le_Rmax : R ≤ Rmax := by
    dsimp [R]
    exact min_le_right _ _
  refine ⟨R, d, D, hR, hR_le_Rmax, hd, hD, ?_, ?_⟩
  · exact Filter.eventually_of_mem hU fun x hx u hu ↦ by
      have huR₀ : u ∈ Metric.ball (0 : E) R₀ :=
        Metric.ball_subset_ball hR_le_R₀ hu
      exact le_of_lt (hUV ⟨hx, hR₀V huR₀⟩).1
  · exact Filter.eventually_of_mem hU fun x hx u hu ↦ by
      have huR₀ : u ∈ Metric.ball (0 : E) R₀ :=
        Metric.ball_subset_ball hR_le_R₀ hu
      exact le_of_lt (hUV ⟨hx, hR₀V huR₀⟩).2

/-- Relative-neighborhood version of
`exists_pos_radius_le_eventually_density_bounds_of_continuousAt_pos`. -/
theorem exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
    {α E : Type*} [TopologicalSpace α] [PseudoMetricSpace E] [Zero E]
    {density : α × E → ℝ} {x₀ : α} {s : Set α} {Rmax : ℝ}
    (hdensity : ContinuousAt density (x₀, 0))
    (hpos : 0 < density (x₀, 0)) (hRmax : 0 < Rmax) :
    ∃ R C : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧
      (∀ᶠ x in nhdsWithin x₀ s,
        ∀ u : E, u ∈ Metric.ball (0 : E) R → 0 ≤ density (x, u)) ∧
      (∀ᶠ x in nhdsWithin x₀ s,
        ∀ u : E, u ∈ Metric.ball (0 : E) R → density (x, u) ≤ C) := by
  rcases exists_pos_radius_le_eventually_density_bounds_of_continuousAt_pos
      hdensity hpos hRmax with
    ⟨R, C, hR, hRle, hC, hnonneg, hle⟩
  exact
    ⟨R, C, hR, hRle, hC,
      (inf_le_left : nhdsWithin x₀ s ≤ nhds x₀) hnonneg,
      (inf_le_left : nhdsWithin x₀ s ≤ nhds x₀) hle⟩

/-- Relative-neighborhood version of
`exists_pos_radius_le_eventually_density_two_sided_bounds_of_continuousAt_pos`. -/
theorem exists_pos_radius_le_eventually_nhdsWithin_density_two_sided_bounds_of_continuousAt_pos
    {α E : Type*} [TopologicalSpace α] [PseudoMetricSpace E] [Zero E]
    {density : α × E → ℝ} {x₀ : α} {s : Set α} {Rmax : ℝ}
    (hdensity : ContinuousAt density (x₀, 0))
    (hpos : 0 < density (x₀, 0)) (hRmax : 0 < Rmax) :
    ∃ R d D : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 < d ∧ 0 ≤ D ∧
      (∀ᶠ x in nhdsWithin x₀ s,
        ∀ u : E, u ∈ Metric.ball (0 : E) R → d ≤ density (x, u)) ∧
      (∀ᶠ x in nhdsWithin x₀ s,
        ∀ u : E, u ∈ Metric.ball (0 : E) R → density (x, u) ≤ D) := by
  rcases exists_pos_radius_le_eventually_density_two_sided_bounds_of_continuousAt_pos
      hdensity hpos hRmax with
    ⟨R, d, D, hR, hRle, hd, hD, hle_lower, hle_upper⟩
  exact
    ⟨R, d, D, hR, hRle, hd, hD,
      (inf_le_left : nhdsWithin x₀ s ≤ nhds x₀) hle_lower,
      (inf_le_left : nhdsWithin x₀ s ≤ nhds x₀) hle_upper⟩

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

/-- A property holding eventually in `nhds x₀` holds a.e. after restricting
any measure to a sufficiently small open neighborhood. -/
theorem exists_open_ae_restrict_of_eventually_nhds
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α} {x₀ : α} {p : α → Prop}
    (hp : ∀ᶠ x in nhds x₀, p x) :
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      ∀ᵐ x ∂ μ.restrict U, p x := by
  rcases mem_nhds_iff.mp hp with ⟨U, hUsub, hUopen, hx₀U⟩
  exact
    ⟨U, hUopen, hx₀U,
      ae_restrict_of_forall_mem hUopen.measurableSet
        (fun x hx => hUsub hx)⟩

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

/-- A real density bounded above and below a.e. gives a two-sided measure
sandwich for the corresponding `ENNReal.ofReal` weighted measure. -/
theorem withDensity_ofReal_sandwich_of_ae_bounds
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {ε K : ℝ}
    (hlower : ∀ᵐ x ∂μ, ε ≤ f x)
    (hupper : ∀ᵐ x ∂μ, f x ≤ K) :
    ENNReal.ofReal ε • μ ≤
        μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) ≤
        ENNReal.ofReal K • μ := by
  constructor
  · rw [← withDensity_const (μ := μ) (ENNReal.ofReal ε)]
    exact
      withDensity_mono
        (hlower.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx)
  · rw [← withDensity_const (μ := μ) (ENNReal.ofReal K)]
    exact
      withDensity_mono
        (hupper.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx)

end Aoyagi
end DLN
end DLNFibre

end
