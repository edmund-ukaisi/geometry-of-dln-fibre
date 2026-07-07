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

It does not construct Aoyagi's p. 13 product chart, compare losses, or
transport Jacobian/density factors.  The finite-lintegral lemmas here are
measure-theoretic domination handoffs, not Aoyagi-specific integrability
theorems.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- A product-neighborhood event contains a measurable product neighborhood.

This is useful when a pointwise bound is known eventually at a product point
and a downstream measure theorem needs rectangular source pieces. -/
theorem exists_measurableSet_prod_subset_of_mem_nhds_prod
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [MeasurableSpace α] [BorelSpace α] [MeasurableSpace β] [BorelSpace β]
    {a : α} {b : β} {S : Set (α × β)}
    (hS : S ∈ nhds (a, b)) :
    ∃ U : Set α, ∃ V : Set β,
      MeasurableSet U ∧ MeasurableSet V ∧
        a ∈ U ∧ b ∈ V ∧ U ×ˢ V ⊆ S := by
  rcases mem_nhds_prod_iff.mp hS with ⟨U, hU, V, hV, hUV⟩
  rcases mem_nhds_iff.mp hU with ⟨U₀, hU₀_sub, hU₀_open, haU₀⟩
  rcases mem_nhds_iff.mp hV with ⟨V₀, hV₀_sub, hV₀_open, hbV₀⟩
  refine ⟨U₀, V₀, hU₀_open.measurableSet, hV₀_open.measurableSet,
    haU₀, hbV₀, ?_⟩
  intro z hz
  exact hUV ⟨hU₀_sub hz.1, hV₀_sub hz.2⟩

/-- Push a density depending only on the image variable through a measurable
map.

This is the reusable measure-theoretic bookkeeping lemma used when a local
coordinate measure is first expressed on a source domain and then pushed
through a chart. -/
theorem measure_map_withDensity_comp_of_aemeasurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {η : Measure α} {f : α → β} {g : β → ℝ≥0∞}
    (hf : AEMeasurable f η)
    (hg : AEMeasurable g (Measure.map f η)) :
    Measure.map f (η.withDensity (fun x ↦ g (f x))) =
      (Measure.map f η).withDensity g := by
  ext t ht
  have hf_density :
      AEMeasurable f (η.withDensity (fun x ↦ g (f x))) :=
    hf.mono_ac (withDensity_absolutelyContinuous _ _)
  have hpre : NullMeasurableSet (f ⁻¹' t) η :=
    hf.nullMeasurableSet_preimage ht
  rw [Measure.map_apply_of_aemeasurable hf_density ht,
    withDensity_apply _ ht, withDensity_apply₀ _ hpre]
  calc
    ∫⁻ x in f ⁻¹' t, g (f x) ∂η =
        ∫⁻ x, (f ⁻¹' t).indicator (fun x ↦ g (f x)) x ∂η := by
          rw [lintegral_indicator₀ hpre]
    _ = ∫⁻ x, (t.indicator g) (f x) ∂η := by
          rfl
    _ = ∫⁻ y, t.indicator g y ∂Measure.map f η := by
          exact (lintegral_map' (hg.indicator ht) hf).symm
    _ = ∫⁻ y in t, g y ∂Measure.map f η := by
          rw [lintegral_indicator ht]

/-- If a composite map is a.e. measurable on a restricted source set, then
the source set intersected with a target-domain chart-piece preimage is
null-measurable. -/
theorem nullMeasurableSet_inter_preimage_inter_of_aemeasurable_comp
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {S : Set α} {T : Set β} {φ : α → β} {χ : β → γ}
    {C : Set γ}
    (hS : NullMeasurableSet S μ)
    (hcomp : AEMeasurable (fun x ↦ χ (φ x)) (μ.restrict S))
    (hmaps : Set.MapsTo φ S T)
    (hC : MeasurableSet C) :
    NullMeasurableSet (S ∩ φ ⁻¹' (T ∩ χ ⁻¹' C)) μ := by
  have hpre :
      NullMeasurableSet ((fun x ↦ χ (φ x)) ⁻¹' C) (μ.restrict S) :=
    hcomp.nullMeasurableSet_preimage hC
  have hpre_lift :
      NullMeasurableSet (((fun x ↦ χ (φ x)) ⁻¹' C) ∩ S) μ :=
    (nullMeasurableSet_restrict hS).1 hpre
  have hsets :
      ((fun x ↦ χ (φ x)) ⁻¹' C) ∩ S =
        S ∩ φ ⁻¹' (T ∩ χ ⁻¹' C) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2, ⟨hmaps hx.2, hx.1⟩⟩
    · intro hx
      exact ⟨hx.2.2, hx.1⟩
  rw [← hsets]
  exact hpre_lift

/-- Push a restricted weighted measure through a map when the source density
factors through that map almost everywhere.

This is the raw-image form of the density handoff: it identifies the
pushforward of `(thetaMeasure.withDensity thetaDensity).restrict V` with a
`withDensity` perturbation of the raw-image measure
`Measure.map rawMap (thetaMeasure.restrict V)`. -/
theorem measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq
    {Θ Raw : Type*} [MeasurableSpace Θ] [MeasurableSpace Raw]
    {thetaMeasure : Measure Θ} {V : Set Θ}
    {rawMap : Θ → Raw}
    {thetaDensity : Θ → ℝ≥0∞} {rawDensity : Raw → ℝ≥0∞}
    (hV : MeasurableSet V)
    (hrawMap : AEMeasurable rawMap (thetaMeasure.restrict V))
    (hrawDensity :
      AEMeasurable rawDensity (Measure.map rawMap (thetaMeasure.restrict V)))
    (hfactor :
      ∀ᵐ theta ∂thetaMeasure.restrict V,
        thetaDensity theta = rawDensity (rawMap theta)) :
    Measure.map rawMap ((thetaMeasure.withDensity thetaDensity).restrict V) =
      (Measure.map rawMap (thetaMeasure.restrict V)).withDensity rawDensity := by
  rw [restrict_withDensity hV]
  rw [withDensity_congr_ae hfactor]
  exact measure_map_withDensity_comp_of_aemeasurable hrawMap hrawDensity

/-- Restricted two-stage version of
`measure_map_withDensity_comp_of_aemeasurable`.

If the two-stage chart pushforward already agrees with a direct source chart
after weighting and restricting the theta measure, then the same source measure
is obtained by first pushing the restricted theta reference through `rawMap`
and then adding the raw density. -/
theorem measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict
    {Θ Raw E : Type*} [MeasurableSpace Θ] [MeasurableSpace Raw]
    [MeasurableSpace E]
    {thetaMeasure : Measure Θ} {V : Set Θ}
    {rawMap : Θ → Raw} {rawChart : Raw → E} {sourceChart : Θ → E}
    {rawDensity : Raw → ℝ≥0∞}
    (hV : MeasurableSet V)
    (hrawMap : AEMeasurable rawMap (thetaMeasure.restrict V))
    (hrawDensity :
      AEMeasurable rawDensity (Measure.map rawMap (thetaMeasure.restrict V)))
    (htwoStage :
      Measure.map rawChart
          (Measure.map rawMap
            ((thetaMeasure.withDensity
              (fun z ↦ rawDensity (rawMap z))).restrict V)) =
        Measure.map sourceChart
          ((thetaMeasure.withDensity
            (fun z ↦ rawDensity (rawMap z))).restrict V)) :
    Measure.map rawChart
        ((Measure.map rawMap (thetaMeasure.restrict V)).withDensity rawDensity) =
      Measure.map sourceChart
        ((thetaMeasure.withDensity
          (fun z ↦ rawDensity (rawMap z))).restrict V) := by
  have htwoStage' :
      Measure.map rawChart
          (Measure.map rawMap
            ((thetaMeasure.restrict V).withDensity
              (fun z ↦ rawDensity (rawMap z)))) =
        Measure.map sourceChart
          ((thetaMeasure.restrict V).withDensity
            (fun z ↦ rawDensity (rawMap z))) := by
    simpa [restrict_withDensity hV] using htwoStage
  have hmain :
      Measure.map rawChart
          ((Measure.map rawMap (thetaMeasure.restrict V)).withDensity rawDensity) =
        Measure.map sourceChart
          ((thetaMeasure.restrict V).withDensity
            (fun z ↦ rawDensity (rawMap z))) := by
    rw [← measure_map_withDensity_comp_of_aemeasurable hrawMap hrawDensity]
    exact htwoStage'
  simpa [restrict_withDensity hV] using hmain

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

/-- A strict upper bound at a continuity point gives the corresponding
eventual non-strict upper bound for an `ℝ≥0∞`-valued function. -/
theorem eventually_le_const_ennreal_of_continuousAt_lt
    {α : Type*} [TopologicalSpace α]
    {f : α → ℝ≥0∞} {z₀ : α} {C : ℝ≥0∞}
    (hf : ContinuousAt f z₀) (hC : f z₀ < C) :
    ∀ᶠ z in nhds z₀, f z ≤ C := by
  have hnbd : Set.Iio C ∈ nhds (f z₀) :=
    isOpen_Iio.mem_nhds hC
  exact
    (show ∀ᶠ z in nhds z₀, f z ∈ Set.Iio C from hf hnbd).mono
      fun _ hz ↦ le_of_lt hz

/-- A finite `ℝ≥0∞` value of a continuous function has a finite eventual
upper bound. -/
theorem exists_lt_top_eventually_le_of_continuousAt_lt_top
    {α : Type*} [TopologicalSpace α]
    {f : α → ℝ≥0∞} {z₀ : α}
    (hf : ContinuousAt f z₀) (hfinite : f z₀ < ∞) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ᶠ z in nhds z₀, f z ≤ C := by
  let C : ℝ≥0∞ := f z₀ + 1
  have hCfinite : C < ∞ := by
    dsimp [C]
    exact ENNReal.add_lt_top.2 ⟨hfinite, ENNReal.one_lt_top⟩
  have hstrict : f z₀ < C := by
    dsimp [C]
    exact ENNReal.lt_add_right hfinite.ne (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
  exact
    ⟨C, hCfinite,
      eventually_le_const_ennreal_of_continuousAt_lt hf hstrict⟩

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

/-- A continuous `ℝ≥0∞` density finite at the base point is bounded a.e. after
restricting to some open neighborhood of that point. -/
theorem exists_open_ae_restrict_le_of_continuousAt_lt_top
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} {z₀ : α}
    (hf : ContinuousAt f z₀) (hfinite : f z₀ < ∞) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∃ V : Set α,
      IsOpen V ∧ z₀ ∈ V ∧ ∀ᵐ z ∂ μ.restrict V, f z ≤ C := by
  rcases exists_lt_top_eventually_le_of_continuousAt_lt_top hf hfinite with
    ⟨C, hCfinite, hCeventually⟩
  rcases exists_open_ae_restrict_of_eventually_nhds
      (μ := μ) (x₀ := z₀) hCeventually with
    ⟨V, hVopen, hz₀V, hVae⟩
  exact ⟨C, hCfinite, V, hVopen, hz₀V, hVae⟩

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

/-- A local a.e. lower bound on a density gives scalar domination of the
unweighted restricted measure by the weighted restricted measure. -/
theorem smul_restrict_le_restrict_withDensity_of_ae_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    {s : Set α} {c : ℝ≥0∞}
    (hs : MeasurableSet s)
    (hf : ∀ᵐ x ∂μ.restrict s, c ≤ f x) :
    c • μ.restrict s ≤ (μ.withDensity f).restrict s := by
  rw [restrict_withDensity hs]
  rw [← withDensity_const (μ := μ.restrict s) c]
  exact withDensity_mono hf

/-- If a reference measure is a weighted restricted measure and the weight is
bounded below up to a finite scalar, then the unweighted restricted measure is
dominated by that scalar multiple of the reference measure.

The lower bound is stated as `1 ≤ C * f x`, avoiding division in `ℝ≥0∞`.
This is the scalar-domination handoff used when a future chart-Jacobian
identity supplies an endpoint image measure as `(μ.restrict s).withDensity f`.
-/
theorem restrict_le_smul_of_eq_withDensity_of_one_le_mul_density
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {f : α → ℝ≥0∞}
    {s : Set α} {C : ℝ≥0∞}
    (hν : ν = (μ.restrict s).withDensity f)
    (hC : C < ∞)
    (hlower : ∀ᵐ x ∂μ.restrict s, 1 ≤ C * f x) :
    μ.restrict s ≤ C • ν := by
  rw [hν]
  calc
    μ.restrict s = (μ.restrict s).withDensity 1 := by
      rw [withDensity_one]
    _ ≤ (μ.restrict s).withDensity (fun x ↦ C * f x) := by
      exact withDensity_mono hlower
    _ = C • (μ.restrict s).withDensity f := by
      have hC_ne_top : C ≠ ∞ := ne_of_lt hC
      simpa [Pi.smul_apply, smul_eq_mul] using
        (withDensity_smul' (μ := μ.restrict s) C f hC_ne_top)

/-- A property that holds a.e. for `μ` also holds a.e. for any measure
dominated by a scalar multiple of `μ`. -/
theorem ae_of_measure_le_smul
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    {p : α → Prop}
    (hν : ν ≤ c • μ)
    (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂ν, p x :=
  (Measure.absolutelyContinuous_of_le_smul hν).ae_le hp

/-- Nullity of a set transfers to any measure dominated by a scalar multiple
of the reference measure. -/
theorem measure_zero_of_measure_le_smul_of_measure_zero
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    {s : Set α}
    (hν : ν ≤ c • μ)
    (hzero : μ s = 0) :
    ν s = 0 := by
  have hle : ν s ≤ (c • μ) s := hν s
  have htarget : (c • μ) s = 0 := by
    simp [Measure.smul_apply, hzero]
  exact le_antisymm (by simpa [htarget] using hle) bot_le

/-- If a real-valued function is positive a.e. for a reference measure, then
any scalar-dominated measure gives zero mass to its zero locus. -/
theorem measure_zero_set_eq_zero_of_measure_le_smul_of_ae_pos
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    {f : α → ℝ}
    (hν : ν ≤ c • μ)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    ν {x | f x = 0} = 0 := by
  have hzero_ref : μ {x | f x = 0} = 0 := by
    rw [ae_iff] at hpos
    exact
      measure_mono_null
        (fun x hx ↦ by
          change ¬ 0 < f x
          rw [hx]
          exact not_lt_of_ge le_rfl)
        hpos
  exact measure_zero_of_measure_le_smul_of_measure_zero hν hzero_ref

/-- Invert a nonzero `ℝ≥0` scalar equality of measures. -/
theorem measure_eq_inv_smul_of_eq_nnreal_smul
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : NNReal}
    (hc : c ≠ 0) (hμ : μ = c • ν) :
    ν = c⁻¹ • μ := by
  rw [hμ]
  ext s
  rw [Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply]
  rw [ENNReal.coe_inv hc]
  rw [← mul_assoc, ENNReal.inv_mul_cancel]
  · simp
  · exact ENNReal.coe_ne_zero.mpr hc
  · exact ENNReal.coe_ne_top

/-- Invert a nonzero finite scalar domination of measures. -/
theorem measure_le_inv_smul_of_smul_le
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hμ : c • μ ≤ ν) :
    μ ≤ c⁻¹ • ν := by
  refine Measure.le_iff.2 ?_
  intro s _hs
  have hs_le : c * μ s ≤ ν s := by
    simpa [Measure.smul_apply] using hμ s
  calc
    μ s = c⁻¹ * (c * μ s) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ ≤ c⁻¹ * ν s := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_right hs_le c⁻¹
    _ = (c⁻¹ • ν) s := by
      simp [Measure.smul_apply, smul_eq_mul]

/-- Finite lower integral transfers to any measure dominated by a finite scalar
multiple of the original measure. -/
theorem lintegral_lt_top_of_measure_le_smul
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    {f : α → ℝ≥0∞}
    (hν : ν ≤ c • μ)
    (hc : c < ∞)
    (hfinite : (∫⁻ x, f x ∂μ) < ∞) :
    (∫⁻ x, f x ∂ν) < ∞ := by
  have hmono :
      (∫⁻ x, f x ∂ν) ≤ (∫⁻ x, f x ∂(c • μ)) :=
    lintegral_mono' hν (le_refl f)
  have htarget : (∫⁻ x, f x ∂(c • μ)) < ∞ := by
    rw [lintegral_smul_measure]
    exact ENNReal.mul_lt_top hc hfinite
  exact hmono.trans_lt htarget

/-- A.e. properties and finite lower integrals transfer together to any
measure dominated by a finite scalar multiple of the original measure. -/
theorem ae_and_lintegral_lt_top_of_measure_le_smul
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    {p : α → Prop} {f : α → ℝ≥0∞}
    (hν : ν ≤ c • μ)
    (hc : c < ∞)
    (hp : ∀ᵐ x ∂μ, p x)
    (hfinite : (∫⁻ x, f x ∂μ) < ∞) :
    (∀ᵐ x ∂ν, p x) ∧ (∫⁻ x, f x ∂ν) < ∞ :=
  ⟨ae_of_measure_le_smul hν hp,
    lintegral_lt_top_of_measure_le_smul hν hc hfinite⟩

/-- Finite-scalar domination of the left measure lifts to product measures
with any fixed s-finite right measure. -/
theorem prod_le_smul_prod_of_le_smul_left
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} (η : Measure β) [SFinite η] {c : ℝ≥0∞}
    (hν : ν ≤ c • μ) :
    ν.prod η ≤ c • μ.prod η := by
  refine Measure.le_iff.2 ?_
  intro s hs
  rw [Measure.prod_apply hs, Measure.smul_apply, Measure.prod_apply hs]
  let f : α → ℝ≥0∞ := fun x ↦ η (Prod.mk x ⁻¹' s)
  calc
    ∫⁻ x, η (Prod.mk x ⁻¹' s) ∂ν ≤ ∫⁻ x, f x ∂(c • μ) :=
      lintegral_mono' hν (le_refl f)
    _ = c * ∫⁻ x, η (Prod.mk x ⁻¹' s) ∂μ := by
      simp [lintegral_smul_measure, f]

/-- A local domination on the left factor of a two-level product lifts to a
domination on any local set supported in the left-factor patch and in a
right-factor cylinder. -/
theorem prod_prod_restrict_le_smul_restrict_cylinder_of_left_restrict_le_smul_of_subset
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ ν : Measure α} {η : Measure β} {κ : Measure γ}
    [SFinite μ] [SFinite η] [SFinite κ]
    {P : Set α} {Q : Set γ} {V : Set ((α × β) × γ)} {c : ℝ≥0∞}
    (hleft : μ.restrict P ≤ c • ν)
    (hV_left : V ⊆ {z : (α × β) × γ | z.1.1 ∈ P})
    (hV_right : V ⊆ {z : (α × β) × γ | z.2 ∈ Q}) :
    ((μ.prod η).prod κ).restrict V ≤
      c • ((((ν.prod η).prod κ).restrict
        {z : (α × β) × γ | z.2 ∈ Q}).restrict V) := by
  have hprod_left :
      (μ.restrict P).prod η ≤ c • ν.prod η :=
    prod_le_smul_prod_of_le_smul_left (η := η) hleft
  have hprod :
      ((μ.restrict P).prod η).prod κ ≤
        c • ((ν.prod η).prod κ) := by
    simpa [Measure.smul_apply] using
      prod_le_smul_prod_of_le_smul_left (η := κ) hprod_left
  have hleftSet :
      ({z : (α × β) × γ | z.1.1 ∈ P} : Set ((α × β) × γ)) =
        (P ×ˢ Set.univ) ×ˢ Set.univ := by
    ext z
    simp
  have hrestrict_left :
      ((μ.prod η).prod κ).restrict {z : (α × β) × γ | z.1.1 ∈ P} =
        ((μ.restrict P).prod η).prod κ := by
    rw [hleftSet]
    rw [← Measure.restrict_prod_eq_prod_univ
      (μ := μ.prod η) (ν := κ) (s := P ×ˢ Set.univ)]
    rw [← Measure.restrict_prod_eq_prod_univ (μ := μ) (ν := η) (s := P)]
  calc
    ((μ.prod η).prod κ).restrict V =
        (((μ.prod η).prod κ).restrict
          {z : (α × β) × γ | z.1.1 ∈ P}).restrict V := by
          exact (Measure.restrict_restrict_of_subset hV_left).symm
    _ = (((μ.restrict P).prod η).prod κ).restrict V := by
          rw [hrestrict_left]
    _ ≤ (c • ((ν.prod η).prod κ)).restrict V :=
          Measure.restrict_mono Set.Subset.rfl hprod
    _ = c • (((ν.prod η).prod κ).restrict V) := by
          rw [Measure.restrict_smul]
    _ = c • ((((ν.prod η).prod κ).restrict
          {z : (α × β) × γ | z.2 ∈ Q}).restrict V) := by
          rw [Measure.restrict_restrict_of_subset hV_right]

/-- A property that holds a.e. for `μ.prod η` also holds a.e. after replacing
the left measure by one dominated by a scalar multiple of `μ`, with `η`
s-finite. -/
theorem ae_prod_of_left_measure_le_smul
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} {η : Measure β} [SFinite η] {c : ℝ≥0∞}
    {p : α × β → Prop}
    (hν : ν ≤ c • μ)
    (hp : ∀ᵐ z ∂μ.prod η, p z) :
    ∀ᵐ z ∂ν.prod η, p z :=
  ae_of_measure_le_smul
    (prod_le_smul_prod_of_le_smul_left (η := η) hν) hp

/-- Finite product lower integrals transfer after replacing the left measure
by one dominated by a finite scalar multiple, with s-finite right measure. -/
theorem lintegral_prod_lt_top_of_left_measure_le_smul
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} {η : Measure β} [SFinite η] {c : ℝ≥0∞}
    {f : α × β → ℝ≥0∞}
    (hν : ν ≤ c • μ)
    (hc : c < ∞)
    (hfinite : (∫⁻ z, f z ∂μ.prod η) < ∞) :
    (∫⁻ z, f z ∂ν.prod η) < ∞ :=
  lintegral_lt_top_of_measure_le_smul
    (prod_le_smul_prod_of_le_smul_left (η := η) hν) hc hfinite

/-- The lower integral against a product with a right Dirac mass is the lower
integral over the left factor with the right coordinate fixed. -/
theorem lintegral_prod_dirac_right
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (y : β) (μ : Measure α)
    [SFinite μ]
    (f : α × β → ℝ≥0∞) :
    (∫⁻ z : α × β, f z ∂ μ.prod (Measure.dirac y)) =
      ∫⁻ x : α, f (x, y) ∂ μ := by
  rw [Measure.prod_dirac]
  exact (measurableEmbedding_prod_mk_right y).lintegral_map (μ := μ) f

universe uβ

/-- Specialize an arbitrary product finite-integral transfer to the
one-factor case by inserting a Dirac mass on a one-point type. -/
theorem lintegral_lt_top_of_forall_prod_transfer_unit
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    {θμ : Measure Θ} {μ : Measure E} {sourceChart : Θ → E}
    [SFinite θμ] [SFinite μ]
    {f : E → ℝ≥0∞}
    (htransfer :
      ∀ {β : Type uβ} [MeasurableSpace β] {ν : Measure β} [SFinite ν]
        {F : E × β → ℝ≥0∞},
        Measurable (fun z : Θ × β ↦ F (sourceChart z.1, z.2)) →
          (∫⁻ z : Θ × β, F (sourceChart z.1, z.2) ∂ θμ.prod ν) < ∞ →
            (∫⁻ z : E × β, F z ∂ μ.prod ν) < ∞)
    (hf_source : Measurable (fun z : Θ ↦ f (sourceChart z)))
    (hfinite_source : (∫⁻ z : Θ, f (sourceChart z) ∂ θμ) < ∞) :
    (∫⁻ z : E, f z ∂ μ) < ∞ := by
  let F : E × PUnit.{uβ + 1} → ℝ≥0∞ := fun z ↦ f z.1
  have hF_source :
      Measurable
        (fun z : Θ × PUnit.{uβ + 1} ↦ F (sourceChart z.1, z.2)) := by
    simpa [F] using hf_source.comp measurable_fst
  have hfinite_source_prod :
      (∫⁻ z : Θ × PUnit.{uβ + 1}, F (sourceChart z.1, z.2) ∂
        θμ.prod (Measure.dirac (PUnit.unit : PUnit.{uβ + 1}))) < ∞ := by
    rw [lintegral_prod_dirac_right (PUnit.unit : PUnit.{uβ + 1})]
    simpa [F] using hfinite_source
  have hfinite_target_prod :
      (∫⁻ z : E × PUnit.{uβ + 1}, F z ∂
        μ.prod (Measure.dirac (PUnit.unit : PUnit.{uβ + 1}))) < ∞ :=
    htransfer (β := PUnit.{uβ + 1})
      (ν := Measure.dirac (PUnit.unit : PUnit.{uβ + 1}))
      (F := F) hF_source hfinite_source_prod
  rw [lintegral_prod_dirac_right (PUnit.unit : PUnit.{uβ + 1})] at hfinite_target_prod
  simpa [F] using hfinite_target_prod

/-- Finite product lower integrals transfer through a readback map whose
pushforward is dominated by a finite scalar multiple of a source measure.

This is pure measure bookkeeping for local source/readback handoffs.  The
right-inverse hypothesis identifies the edge-family integrand with the
source-chart pullback after readback, while the map-domination hypothesis
transfers the finite source integral. -/
theorem lintegral_prod_lt_top_of_readback_map_le_smul
    {Θ E β : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    [MeasurableSpace β]
    {μ : Measure E} [SFinite μ] {θμ : Measure Θ} {η : Measure β}
    [SFinite η] {readback : E → Θ} {sourceChart : Θ → E}
    {C : ℝ≥0∞} {F : E × β → ℝ≥0∞}
    (hreadback : Measurable readback)
    (hright : ∀ᵐ x ∂μ, sourceChart (readback x) = x)
    (hmap : Measure.map readback μ ≤ C • θμ)
    (hC : C < ∞)
    (hFsource : Measurable (fun z : Θ × β ↦ F (sourceChart z.1, z.2)))
    (hfinite :
      (∫⁻ z : Θ × β, F (sourceChart z.1, z.2) ∂θμ.prod η) < ∞) :
    (∫⁻ z : E × β, F z ∂μ.prod η) < ∞ := by
  let Fsource : Θ × β → ℝ≥0∞ :=
    fun z ↦ F (sourceChart z.1, z.2)
  let readbackProd : E × β → Θ × β := Prod.map readback id
  have hmap_prod :
      (Measure.map readback μ).prod η =
        Measure.map readbackProd (μ.prod η) := by
    simpa [readbackProd] using
      (Measure.map_prod_map μ η hreadback measurable_id)
  have hfinite_map :
      (∫⁻ z : Θ × β, Fsource z ∂(Measure.map readback μ).prod η) < ∞ :=
    lintegral_prod_lt_top_of_left_measure_le_smul
      (η := η) hmap hC (by simpa [Fsource] using hfinite)
  have hfinite_comp :
      (∫⁻ z : E × β, Fsource (readbackProd z) ∂μ.prod η) < ∞ := by
    calc
      (∫⁻ z : E × β, Fsource (readbackProd z) ∂μ.prod η) =
          ∫⁻ z : Θ × β, Fsource z ∂Measure.map readbackProd (μ.prod η) := by
        exact (lintegral_map hFsource (hreadback.prodMap measurable_id)).symm
      _ = ∫⁻ z : Θ × β, Fsource z ∂(Measure.map readback μ).prod η := by
        rw [← hmap_prod]
      _ < ∞ := hfinite_map
  have hright_prod :
      ∀ᵐ z : E × β ∂μ.prod η, sourceChart (readback z.1) = z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := η)).ae hright
  have hcongr :
      (∫⁻ z : E × β, F z ∂μ.prod η) =
        ∫⁻ z : E × β, Fsource (readbackProd z) ∂μ.prod η := by
    refine lintegral_congr_ae ?_
    filter_upwards [hright_prod] with z hz
    simp [Fsource, readbackProd, hz]
  simpa [hcongr]
    using hfinite_comp

/-- Finite product lower integrals transfer through an a.e.-measurable
readback map whose pushforward is dominated by a finite scalar multiple of a
source measure.

This is the same handoff as `lintegral_prod_lt_top_of_readback_map_le_smul`,
with the measurability hypothesis weakened to the form returned by localized
readback-domination theorems. -/
theorem lintegral_prod_lt_top_of_aemeasurable_readback_map_le_smul
    {Θ E β : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    [MeasurableSpace β]
    {μ : Measure E} [SFinite μ] {θμ : Measure Θ} {η : Measure β}
    [SFinite η] {readback : E → Θ} {sourceChart : Θ → E}
    {C : ℝ≥0∞} {F : E × β → ℝ≥0∞}
    (hreadback : AEMeasurable readback μ)
    (hright : ∀ᵐ x ∂μ, sourceChart (readback x) = x)
    (hmap : Measure.map readback μ ≤ C • θμ)
    (hC : C < ∞)
    (hFsource : Measurable (fun z : Θ × β ↦ F (sourceChart z.1, z.2)))
    (hfinite :
      (∫⁻ z : Θ × β, F (sourceChart z.1, z.2) ∂θμ.prod η) < ∞) :
    (∫⁻ z : E × β, F z ∂μ.prod η) < ∞ := by
  let Fsource : Θ × β → ℝ≥0∞ :=
    fun z ↦ F (sourceChart z.1, z.2)
  let readbackMk : E → Θ := hreadback.mk readback
  let readbackProd : E × β → Θ × β := fun z ↦ (readback z.1, z.2)
  let readbackProdMk : E × β → Θ × β := Prod.map readbackMk id
  have hreadbackMk : Measurable readbackMk :=
    hreadback.measurable_mk
  have hmap_readback :
      Measure.map readback μ = Measure.map readbackMk μ :=
    Measure.map_congr hreadback.ae_eq_mk
  have hreadbackProd_ae :
      readbackProd =ᵐ[μ.prod η] readbackProdMk := by
    have hfst :
        ∀ᵐ z : E × β ∂μ.prod η, readback z.1 = readbackMk z.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := η)).ae
        hreadback.ae_eq_mk
    filter_upwards [hfst] with z hz
    rcases z with ⟨x, y⟩
    simp [readbackProd, readbackProdMk, hz]
  have hmap_prod :
      (Measure.map readback μ).prod η =
        Measure.map readbackProd (μ.prod η) := by
    calc
      (Measure.map readback μ).prod η =
          (Measure.map readbackMk μ).prod η := by
        rw [hmap_readback]
      _ = Measure.map readbackProdMk (μ.prod η) := by
        simpa [readbackProdMk] using
          (Measure.map_prod_map μ η hreadbackMk measurable_id)
      _ = Measure.map readbackProd (μ.prod η) := by
        exact (Measure.map_congr hreadbackProd_ae).symm
  have hfinite_map :
      (∫⁻ z : Θ × β, Fsource z ∂(Measure.map readback μ).prod η) < ∞ :=
    lintegral_prod_lt_top_of_left_measure_le_smul
      (η := η) hmap hC (by simpa [Fsource] using hfinite)
  have hreadbackProd_aemeas :
      AEMeasurable readbackProd (μ.prod η) := by
    have hfst :
        AEMeasurable (fun z : E × β ↦ readback z.1) (μ.prod η) :=
      hreadback.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := η))
    simpa [readbackProd] using hfst.prodMk measurable_snd.aemeasurable
  have hfinite_comp :
      (∫⁻ z : E × β, Fsource (readbackProd z) ∂μ.prod η) < ∞ := by
    calc
      (∫⁻ z : E × β, Fsource (readbackProd z) ∂μ.prod η) =
          ∫⁻ z : Θ × β, Fsource z ∂Measure.map readbackProd (μ.prod η) := by
        exact (lintegral_map' hFsource.aemeasurable hreadbackProd_aemeas).symm
      _ = ∫⁻ z : Θ × β, Fsource z ∂(Measure.map readback μ).prod η := by
        rw [← hmap_prod]
      _ < ∞ := hfinite_map
  have hright_prod :
      ∀ᵐ z : E × β ∂μ.prod η, sourceChart (readback z.1) = z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := η)).ae hright
  have hcongr :
      (∫⁻ z : E × β, F z ∂μ.prod η) =
        ∫⁻ z : E × β, Fsource (readbackProd z) ∂μ.prod η := by
    refine lintegral_congr_ae ?_
    filter_upwards [hright_prod] with z hz
    simp [Fsource, readbackProd, hz]
  simpa [hcongr]
    using hfinite_comp

/-- Finite product lower integrals transfer through an a.e.-measurable
readback map whose pushforward is dominated by a finite scalar multiple of a
source measure, assuming only source-side a.e.-measurability of the pulled-back
integrand.

This is the same handoff as
`lintegral_prod_lt_top_of_aemeasurable_readback_map_le_smul`, but the
measurability socket is localized to the source measure.  The dominated mapped
measure is absolutely continuous with respect to a scalar multiple of the
source measure, so source-side a.e.-measurability is enough for the
`lintegral_map'` step. -/
theorem lintegral_prod_lt_top_of_aemeasurable_readback_map_le_smul_of_aemeasurable_source
    {Θ E β : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    [MeasurableSpace β]
    {μ : Measure E} [SFinite μ] {θμ : Measure Θ} {η : Measure β}
    [SFinite η] {readback : E → Θ} {sourceChart : Θ → E}
    {C : ℝ≥0∞} {F : E × β → ℝ≥0∞}
    (hreadback : AEMeasurable readback μ)
    (hright : ∀ᵐ x ∂μ, sourceChart (readback x) = x)
    (hmap : Measure.map readback μ ≤ C • θμ)
    (hC : C < ∞)
    (hFsource :
      AEMeasurable (fun z : Θ × β ↦ F (sourceChart z.1, z.2))
        (θμ.prod η))
    (hfinite :
      (∫⁻ z : Θ × β, F (sourceChart z.1, z.2) ∂θμ.prod η) < ∞) :
    (∫⁻ z : E × β, F z ∂μ.prod η) < ∞ := by
  let Fsource : Θ × β → ℝ≥0∞ :=
    fun z ↦ F (sourceChart z.1, z.2)
  let readbackMk : E → Θ := hreadback.mk readback
  let readbackProd : E × β → Θ × β := fun z ↦ (readback z.1, z.2)
  let readbackProdMk : E × β → Θ × β := Prod.map readbackMk id
  have hreadbackMk : Measurable readbackMk :=
    hreadback.measurable_mk
  have hmap_readback :
      Measure.map readback μ = Measure.map readbackMk μ :=
    Measure.map_congr hreadback.ae_eq_mk
  have hreadbackProd_ae :
      readbackProd =ᵐ[μ.prod η] readbackProdMk := by
    have hfst :
        ∀ᵐ z : E × β ∂μ.prod η, readback z.1 = readbackMk z.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := η)).ae
        hreadback.ae_eq_mk
    filter_upwards [hfst] with z hz
    rcases z with ⟨x, y⟩
    simp [readbackProd, readbackProdMk, hz]
  have hmap_prod :
      (Measure.map readback μ).prod η =
        Measure.map readbackProd (μ.prod η) := by
    calc
      (Measure.map readback μ).prod η =
          (Measure.map readbackMk μ).prod η := by
        rw [hmap_readback]
      _ = Measure.map readbackProdMk (μ.prod η) := by
        simpa [readbackProdMk] using
          (Measure.map_prod_map μ η hreadbackMk measurable_id)
      _ = Measure.map readbackProd (μ.prod η) := by
        exact (Measure.map_congr hreadbackProd_ae).symm
  have hfinite_map :
      (∫⁻ z : Θ × β, Fsource z ∂(Measure.map readback μ).prod η) < ∞ :=
    lintegral_prod_lt_top_of_left_measure_le_smul
      (η := η) hmap hC (by simpa [Fsource] using hfinite)
  have hsource_smul :
      AEMeasurable Fsource (C • θμ.prod η) :=
    hFsource.mono_ac Measure.smul_absolutelyContinuous
  have hmap_prod_le :
      (Measure.map readback μ).prod η ≤ C • θμ.prod η :=
    prod_le_smul_prod_of_le_smul_left (η := η) hmap
  have hsource_map :
      AEMeasurable Fsource (Measure.map readbackProd (μ.prod η)) := by
    have hsource_map_left :
        AEMeasurable Fsource ((Measure.map readback μ).prod η) :=
      hsource_smul.mono_measure hmap_prod_le
    rwa [← hmap_prod]
  have hreadbackProd_aemeas :
      AEMeasurable readbackProd (μ.prod η) := by
    have hfst :
        AEMeasurable (fun z : E × β ↦ readback z.1) (μ.prod η) :=
      hreadback.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := η))
    simpa [readbackProd] using hfst.prodMk measurable_snd.aemeasurable
  have hfinite_comp :
      (∫⁻ z : E × β, Fsource (readbackProd z) ∂μ.prod η) < ∞ := by
    calc
      (∫⁻ z : E × β, Fsource (readbackProd z) ∂μ.prod η) =
          ∫⁻ z : Θ × β, Fsource z ∂Measure.map readbackProd (μ.prod η) := by
        exact (lintegral_map' hsource_map hreadbackProd_aemeas).symm
      _ = ∫⁻ z : Θ × β, Fsource z ∂(Measure.map readback μ).prod η := by
        rw [← hmap_prod]
      _ < ∞ := hfinite_map
  have hright_prod :
      ∀ᵐ z : E × β ∂μ.prod η, sourceChart (readback z.1) = z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := η)).ae hright
  have hcongr :
      (∫⁻ z : E × β, F z ∂μ.prod η) =
        ∫⁻ z : E × β, Fsource (readbackProd z) ∂μ.prod η := by
    refine lintegral_congr_ae ?_
    filter_upwards [hright_prod] with z hz
    simp [Fsource, readbackProd, hz]
  simpa [hcongr]
    using hfinite_comp

/-- A measure domination by a scalar multiple remains true after mapping by a
measurable function. -/
theorem map_le_smul_map_of_le_smul
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} {c : ℝ≥0∞} {f : α → β}
    (hf : Measurable f)
    (hν : ν ≤ c • μ) :
    Measure.map f ν ≤ c • Measure.map f μ := by
  calc
    Measure.map f ν ≤ Measure.map f (c • μ) :=
      Measure.map_mono hν hf
    _ = c • Measure.map f μ := by
      rw [Measure.map_smul]

/-- A measure domination by a scalar multiple remains true after mapping by an
a.e. measurable function, with the a.e. measurability checked for the
dominating/reference measure. -/
theorem map_le_smul_map_of_le_smul_aemeasurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} {c : ℝ≥0∞} {f : α → β}
    (hfμ : AEMeasurable f μ)
    (hν : ν ≤ c • μ) :
    Measure.map f ν ≤ c • Measure.map f μ := by
  let f' := AEMeasurable.mk f hfμ
  have hν_ac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
  have hfν_eq : f =ᶠ[ae ν] f' :=
    hν_ac.ae_le hfμ.ae_eq_mk
  have hν_eq : Measure.map f ν = Measure.map f' ν :=
    Measure.map_congr hfν_eq
  have hμ_eq : Measure.map f μ = Measure.map f' μ :=
    Measure.map_congr hfμ.ae_eq_mk
  calc
    Measure.map f ν = Measure.map f' ν := hν_eq
    _ ≤ Measure.map f' (c • μ) :=
      Measure.map_mono hν hfμ.measurable_mk
    _ = c • Measure.map f' μ := by
      rw [Measure.map_smul]
    _ = c • Measure.map f μ := by
      rw [hμ_eq]

/-- Two scalar measure dominations compose by multiplying the scalars. -/
theorem measure_le_smul_of_le_smul_of_le_smul
    {α : Type*} [MeasurableSpace α] {μ ν η : Measure α} {c d : ℝ≥0∞}
    (hμ : μ ≤ c • ν) (hν : ν ≤ d • η) :
    μ ≤ (c * d) • η := by
  have hscale : c • ν ≤ c • (d • η) := by
    refine Measure.le_iff.2 ?_
    intro s _hs
    rw [Measure.smul_apply, Measure.smul_apply]
    exact mul_le_mul_right (hν s) c
  have hassoc : c • (d • η) = (c * d) • η := by
    ext s hs
    simp [Measure.smul_apply, mul_assoc]
  calc
    μ ≤ c • ν := hμ
    _ ≤ c • (d • η) := hscale
    _ = (c * d) • η := hassoc

/-- Compose a domination `η ≤ D • μ` with a lower scalar domination
`c • μ ≤ ν`, paying the inverse scalar `c⁻¹`. -/
theorem measure_le_smul_of_le_smul_of_smul_le
    {α : Type*} [MeasurableSpace α] {η μ ν : Measure α} {D c : ℝ≥0∞}
    (hη : η ≤ D • μ)
    (hμ : c • μ ≤ ν)
    (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    η ≤ (D * c⁻¹) • ν :=
  measure_le_smul_of_le_smul_of_le_smul hη
    (measure_le_inv_smul_of_smul_le hc0 hctop hμ)

/-- If a target measure is dominated by the raw image of a base measure, and
a density is locally bounded below, then it is dominated by the raw image of
the corresponding weighted base measure, with the inverse lower-bound scalar.

This is pure measure bookkeeping: the base domination and the lower density
bound remain explicit hypotheses. -/
theorem measure_le_smul_map_restrict_withDensity_of_le_smul_map_restrict_of_ae_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {base : Measure α} {target : Measure β} {rawMap : α → β}
    {density : α → ℝ≥0∞} {V : Set α} {D ε : ℝ≥0∞}
    (hrawMap :
      AEMeasurable rawMap ((base.withDensity density).restrict V))
    (hV : MeasurableSet V)
    (hbase :
      target ≤ D • Measure.map rawMap (base.restrict V))
    (hlower : ∀ᵐ x ∂base.restrict V, ε ≤ density x)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    target ≤
      (D * ε⁻¹) •
        Measure.map rawMap ((base.withDensity density).restrict V) := by
  have hweighted_base :
      ε • base.restrict V ≤ (base.withDensity density).restrict V :=
    smul_restrict_le_restrict_withDensity_of_ae_le hV hlower
  have hmap_weighted :
      ε • Measure.map rawMap (base.restrict V) ≤
        Measure.map rawMap ((base.withDensity density).restrict V) := by
    have hweighted_base_one :
        ε • base.restrict V ≤
          (1 : ℝ≥0∞) • (base.withDensity density).restrict V := by
      simpa using hweighted_base
    have hmap :
        Measure.map rawMap (ε • base.restrict V) ≤
          (1 : ℝ≥0∞) • Measure.map rawMap
            ((base.withDensity density).restrict V) :=
      map_le_smul_map_of_le_smul_aemeasurable (c := 1) hrawMap
        hweighted_base_one
    simpa [Measure.map_smul] using hmap
  exact
    measure_le_smul_of_le_smul_of_smul_le hbase hmap_weighted hε0 hεtop

/-- Left-factor domination of product measures transfers through restriction
and a map, then composes with a supplied domination of the reference
pushforward.

This is the bookkeeping needed when a future concrete left-factor reference
measure is known to dominate a passive-field measure, and the product
reference has already been compared to a chart-side target measure. -/
theorem map_prod_restrict_le_smul_of_left_le_smul_of_map_prod_restrict_le_smul
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    {μ ν : Measure α} {η : Measure β} [SFinite η]
    {V : Set (α × β)} {f : α × β → γ}
    {target : Measure γ} {c d : ℝ≥0∞}
    (hfν : AEMeasurable f ((ν.prod η).restrict V))
    (hμ : μ ≤ d • ν)
    (href :
      Measure.map f ((ν.prod η).restrict V) ≤ c • target) :
    Measure.map f ((μ.prod η).restrict V) ≤ (d * c) • target := by
  have hprod : μ.prod η ≤ d • ν.prod η :=
    prod_le_smul_prod_of_le_smul_left (η := η) hμ
  have hrestrict :
      (μ.prod η).restrict V ≤ d • (ν.prod η).restrict V := by
    calc
      (μ.prod η).restrict V ≤ (d • ν.prod η).restrict V :=
        Measure.restrict_mono Set.Subset.rfl hprod
      _ = d • (ν.prod η).restrict V := by
        rw [Measure.restrict_smul]
  have hmap :
      Measure.map f ((μ.prod η).restrict V) ≤
        d • Measure.map f ((ν.prod η).restrict V) :=
    map_le_smul_map_of_le_smul_aemeasurable hfν hrestrict
  exact measure_le_smul_of_le_smul_of_le_smul hmap href

/-- A scalar measure domination remains true after weighting both measures by
the same density. -/
theorem withDensity_le_smul_withDensity_of_le_smul
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    {density : α → ℝ≥0∞}
    (hν : ν ≤ c • μ) :
    ν.withDensity density ≤ c • μ.withDensity density := by
  refine Measure.le_iff.2 ?_
  intro s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, withDensity_apply _ hs]
  have hrestrict :
      ν.restrict s ≤ c • μ.restrict s := by
    calc
      ν.restrict s ≤ (c • μ).restrict s :=
        Measure.restrict_mono Set.Subset.rfl hν
      _ = c • μ.restrict s := by
        rw [Measure.restrict_smul]
  calc
    ∫⁻ x, density x ∂ν.restrict s ≤
        ∫⁻ x, density x ∂(c • μ.restrict s) :=
      lintegral_mono' hrestrict (le_refl density)
    _ = c * ∫⁻ x, density x ∂μ.restrict s := by
      simp [lintegral_smul_measure]

/-- Domination of a source pushforward transfers through a second map once the
reference pushforward along that second map has been identified.

This is pure measure bookkeeping.  The hypothesis
`Measure.map pre μ ≤ c • sourceRef` is the substantive chart/source
comparison; the theorem only composes it with `post` and rewrites the
reference pushforward as `targetRef`. -/
theorem map_comp_le_smul_of_map_le_smul_of_map_ref_eq
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {sourceRef : Measure β} {targetRef : Measure γ}
    {c : ℝ≥0∞} {pre : α → β} {post : β → γ}
    (hpre : AEMeasurable pre μ)
    (hpost_ref : AEMeasurable post sourceRef)
    (hpre_dom : Measure.map pre μ ≤ c • sourceRef)
    (hpost_ref_map : Measure.map post sourceRef = targetRef) :
    Measure.map (fun x ↦ post (pre x)) μ ≤ c • targetRef := by
  have hmap_ac : Measure.map pre μ ≪ sourceRef :=
    Measure.absolutelyContinuous_of_le_smul hpre_dom
  have hpost_map_pre : AEMeasurable post (Measure.map pre μ) :=
    hpost_ref.mono_ac hmap_ac
  calc
    Measure.map (fun x ↦ post (pre x)) μ =
        Measure.map post (Measure.map pre μ) := by
          simpa [Function.comp_def] using
            (AEMeasurable.map_map_of_aemeasurable
              (μ := μ) (g := post) (f := pre) hpost_map_pre hpre).symm
    _ ≤ c • Measure.map post sourceRef :=
          map_le_smul_map_of_le_smul_aemeasurable hpost_ref hpre_dom
    _ = c • targetRef := by
          rw [hpost_ref_map]

/-- Weighted domination of a source pushforward transfers through a second map
once the weighted reference pushforward along that second map has been
identified.

This is pure measure bookkeeping.  The substantive hypothesis is
`Measure.map pre μ ≤ c • sourceRef`; the theorem weights both sides by the same
source-side density and then composes with `post`. -/
theorem map_comp_withDensity_comp_le_smul_of_map_le_smul_of_weighted_map_ref_eq
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {sourceRef : Measure β} {targetRef : Measure γ}
    {c : ℝ≥0∞} {pre : α → β} {post : β → γ} {density : β → ℝ≥0∞}
    (hpre : AEMeasurable pre μ)
    (hdensity_ref : AEMeasurable density sourceRef)
    (hpost_ref_weighted : AEMeasurable post (sourceRef.withDensity density))
    (hpre_dom : Measure.map pre μ ≤ c • sourceRef)
    (hpost_ref_map : Measure.map post (sourceRef.withDensity density) = targetRef) :
    Measure.map (fun x ↦ post (pre x))
        (μ.withDensity (fun x ↦ density (pre x))) ≤
      c • targetRef := by
  have hmap_ac : Measure.map pre μ ≪ sourceRef :=
    Measure.absolutelyContinuous_of_le_smul hpre_dom
  have hdensity_map_pre :
      AEMeasurable density (Measure.map pre μ) :=
    hdensity_ref.mono_ac hmap_ac
  have hpre_weighted :
      Measure.map pre (μ.withDensity (fun x ↦ density (pre x))) =
        (Measure.map pre μ).withDensity density :=
    measure_map_withDensity_comp_of_aemeasurable hpre hdensity_map_pre
  have hweighted_dom :
      (Measure.map pre μ).withDensity density ≤
        c • sourceRef.withDensity density :=
    withDensity_le_smul_withDensity_of_le_smul hpre_dom
  have hweighted_ac :
      (Measure.map pre μ).withDensity density ≪ sourceRef.withDensity density :=
    Measure.absolutelyContinuous_of_le_smul hweighted_dom
  have hpre_weighted_aemeasurable :
      AEMeasurable pre (μ.withDensity (fun x ↦ density (pre x))) :=
    hpre.mono_ac (withDensity_absolutelyContinuous _ _)
  have hpost_map_pre :
      AEMeasurable post
        (Measure.map pre (μ.withDensity (fun x ↦ density (pre x)))) := by
    rw [hpre_weighted]
    exact hpost_ref_weighted.mono_ac hweighted_ac
  calc
    Measure.map (fun x ↦ post (pre x))
        (μ.withDensity (fun x ↦ density (pre x))) =
        Measure.map post
          (Measure.map pre (μ.withDensity (fun x ↦ density (pre x)))) := by
          simpa [Function.comp_def] using
            (AEMeasurable.map_map_of_aemeasurable
              (μ := μ.withDensity (fun x ↦ density (pre x)))
              (g := post) (f := pre) hpost_map_pre
              hpre_weighted_aemeasurable).symm
    _ = Measure.map post ((Measure.map pre μ).withDensity density) := by
          rw [hpre_weighted]
    _ ≤ c • Measure.map post (sourceRef.withDensity density) :=
          map_le_smul_map_of_le_smul_aemeasurable
            hpost_ref_weighted hweighted_dom
    _ = c • targetRef := by
          rw [hpost_ref_map]

/-- Reverse weighted domination transfers through a second map once the
weighted source-reference pushforward along that second map has been
identified.

This is pure measure bookkeeping.  The substantive hypothesis is
`sourceRef ≤ c • Measure.map pre μ`; the theorem weights both sides by the same
source-side density and then composes with `post`. -/
theorem weighted_map_ref_le_smul_map_comp_withDensity_comp_of_le_smul_map
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {sourceRef : Measure β} {targetRef : Measure γ}
    {c : ℝ≥0∞} {pre : α → β} {post : β → γ} {density : β → ℝ≥0∞}
    (hpre : AEMeasurable pre μ)
    (hdensity_map_pre : AEMeasurable density (Measure.map pre μ))
    (hpost_map_pre_weighted :
      AEMeasurable post ((Measure.map pre μ).withDensity density))
    (hpre_dom : sourceRef ≤ c • Measure.map pre μ)
    (hpost_ref_map : Measure.map post (sourceRef.withDensity density) = targetRef) :
    targetRef ≤ c •
      Measure.map (fun x ↦ post (pre x))
        (μ.withDensity (fun x ↦ density (pre x))) := by
  have hpre_weighted :
      Measure.map pre (μ.withDensity (fun x ↦ density (pre x))) =
        (Measure.map pre μ).withDensity density :=
    measure_map_withDensity_comp_of_aemeasurable hpre hdensity_map_pre
  have hweighted_dom :
      sourceRef.withDensity density ≤
        c • (Measure.map pre μ).withDensity density :=
    withDensity_le_smul_withDensity_of_le_smul hpre_dom
  have hpre_weighted_aemeasurable :
      AEMeasurable pre (μ.withDensity (fun x ↦ density (pre x))) :=
    hpre.mono_ac (withDensity_absolutelyContinuous _ _)
  have hpost_map_pre :
      AEMeasurable post
        (Measure.map pre (μ.withDensity (fun x ↦ density (pre x)))) := by
    rw [hpre_weighted]
    exact hpost_map_pre_weighted
  have hmap_comp :
      Measure.map post
          (Measure.map pre (μ.withDensity (fun x ↦ density (pre x)))) =
        Measure.map (fun x ↦ post (pre x))
          (μ.withDensity (fun x ↦ density (pre x))) := by
    simpa [Function.comp_def] using
      AEMeasurable.map_map_of_aemeasurable
        (μ := μ.withDensity (fun x ↦ density (pre x)))
        (g := post) (f := pre) hpost_map_pre hpre_weighted_aemeasurable
  calc
    targetRef = Measure.map post (sourceRef.withDensity density) := by
          rw [hpost_ref_map]
    _ ≤ c • Measure.map post ((Measure.map pre μ).withDensity density) :=
          map_le_smul_map_of_le_smul_aemeasurable
            hpost_map_pre_weighted hweighted_dom
    _ = c • Measure.map post
          (Measure.map pre (μ.withDensity (fun x ↦ density (pre x)))) := by
          rw [hpre_weighted]
    _ = c • Measure.map (fun x ↦ post (pre x))
          (μ.withDensity (fun x ↦ density (pre x))) := by
          rw [hmap_comp]

/-- Readback domination transfers from a source reference measure to any
measure dominated by that source reference. -/
theorem readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    {sourceRef μ : Measure E} {thetaRef : Measure Θ} {C : ℝ≥0∞}
    {readback : E → Θ}
    (hreadback_source : AEMeasurable readback sourceRef)
    (hsource_pull : Measure.map readback sourceRef = thetaRef)
    (hμ : μ ≤ C • sourceRef) :
    AEMeasurable readback μ ∧ Measure.map readback μ ≤ C • thetaRef := by
  have hμ_ac : μ ≪ sourceRef := Measure.absolutelyContinuous_of_le_smul hμ
  have hreadback_μ : AEMeasurable readback μ :=
    hreadback_source.mono_ac hμ_ac
  have hmap :
      Measure.map readback μ ≤ C • Measure.map readback sourceRef :=
    map_le_smul_map_of_le_smul_aemeasurable hreadback_source hμ
  exact ⟨hreadback_μ, by simpa [hsource_pull] using hmap⟩

/-- Readback domination transfers from a source reference measure to any
measure dominated by that source reference, allowing the source reference
itself to pull back only up to scalar domination.

This is pure measure bookkeeping.  It does not identify the source reference
or prove any chart-image or source-coverage statement. -/
theorem readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le
    {Θ E : Type*} [MeasurableSpace Θ] [MeasurableSpace E]
    {sourceRef μ : Measure E} {thetaRef : Measure Θ} {C Csource : ℝ≥0∞}
    {readback : E → Θ}
    (hreadback_source : AEMeasurable readback sourceRef)
    (hsource_pull_le : Measure.map readback sourceRef ≤ Csource • thetaRef)
    (hμ : μ ≤ C • sourceRef) :
    AEMeasurable readback μ ∧
      Measure.map readback μ ≤ (C * Csource) • thetaRef := by
  have hμ_ac : μ ≪ sourceRef := Measure.absolutelyContinuous_of_le_smul hμ
  have hreadback_μ : AEMeasurable readback μ :=
    hreadback_source.mono_ac hμ_ac
  have hmap :
      Measure.map readback μ ≤ C • Measure.map readback sourceRef :=
    map_le_smul_map_of_le_smul_aemeasurable hreadback_source hμ
  exact ⟨hreadback_μ,
    measure_le_smul_of_le_smul_of_le_smul hmap hsource_pull_le⟩

/-- If a measure is dominated by a scalar multiple of a restricted measure,
then it is dominated by the same scalar multiple of the original measure. -/
theorem measure_le_smul_of_le_smul_restrict
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    {U : Set α}
    (hν : ν ≤ c • μ.restrict U) :
    ν ≤ c • μ := by
  refine hν.trans ?_
  exact Measure.le_iff.2 fun s hs ↦ by
    rw [Measure.smul_apply, Measure.smul_apply]
    exact mul_le_mul_right (Measure.restrict_le_self s) c

/-- If the left measure is supported on `U`, a scalar domination by `μ`
upgrades to scalar domination by `μ.restrict U`. -/
theorem measure_le_smul_restrict_of_le_smul_of_restrict_eq_self
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    {U : Set α}
    (hν : ν ≤ c • μ)
    (hsupport : ν.restrict U = ν) :
    ν ≤ c • μ.restrict U := by
  refine Measure.le_iff.2 ?_
  intro s hs
  calc
    ν s = (ν.restrict U) s := by rw [hsupport]
    _ = ν (s ∩ U) := by rw [Measure.restrict_apply hs]
    _ ≤ (c • μ) (s ∩ U) := hν (s ∩ U)
    _ = c • μ (s ∩ U) := by rw [Measure.smul_apply]
    _ = c • (μ.restrict U) s := by rw [Measure.restrict_apply hs]
    _ = (c • μ.restrict U) s := by rw [Measure.smul_apply]

/-- Restricting a measure to a set and then to a containing set does not
change the already restricted measure. -/
theorem restrict_restrict_eq_self_of_subset
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}
    (hs : MeasurableSet s) (hst : s ⊆ t) :
    (μ.restrict s).restrict t = μ.restrict s := by
  exact
    Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hs).mono fun x hx ↦ hst hx)

/-- A scalar domination of a restricted measure upgrades to domination by the
same scalar multiple of a larger restricted reference measure. -/
theorem restrict_le_smul_restrict_of_le_smul_of_subset
    {α : Type*} [MeasurableSpace α] {μ η : Measure α} {c : ℝ≥0∞}
    {s t : Set α}
    (hs : MeasurableSet s) (hst : s ⊆ t)
    (hμ : μ.restrict s ≤ c • η) :
    μ.restrict s ≤ c • η.restrict t :=
  measure_le_smul_restrict_of_le_smul_of_restrict_eq_self hμ
    (restrict_restrict_eq_self_of_subset hs hst)

/-- A local a.e. upper bound on a density gives scalar domination by the same
restricted reference measure. -/
theorem restrict_withDensity_le_smul_restrict_of_ae_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    {s : Set α} {c : ℝ≥0∞}
    (hs : MeasurableSet s)
    (hf : ∀ᵐ x ∂μ.restrict s, f x ≤ c) :
    (μ.withDensity f).restrict s ≤ c • μ.restrict s := by
  rw [restrict_withDensity hs]
  rw [← withDensity_const (μ := μ.restrict s) c]
  exact withDensity_mono hf

/-- A local a.e. upper bound on a density gives scalar domination by the
same restricted reference measure enlarged to any containing set. -/
theorem restrict_withDensity_le_smul_restrict_of_ae_le_of_subset
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    {s t : Set α} {c : ℝ≥0∞}
    (hs : MeasurableSet s) (hst : s ⊆ t)
    (hf : ∀ᵐ x ∂μ.restrict s, f x ≤ c) :
    (μ.withDensity f).restrict s ≤ c • μ.restrict t := by
  have hlocal :
      (μ.withDensity f).restrict s ≤ c • μ.restrict s :=
    restrict_withDensity_le_smul_restrict_of_ae_le hs hf
  refine hlocal.trans ?_
  have hrestrict : μ.restrict s ≤ μ.restrict t :=
    Measure.restrict_mono hst le_rfl
  exact Measure.le_iff.2 fun u _ ↦ by
    rw [Measure.smul_apply, Measure.smul_apply]
    exact mul_le_mul_right (hrestrict u) c

/-- A local a.e. upper bound on a density gives scalar domination after
restricting the weighted measure to that local set. -/
theorem restrict_withDensity_le_smul_of_ae_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    {s : Set α} {c : ℝ≥0∞}
    (hs : MeasurableSet s)
    (hf : ∀ᵐ x ∂μ.restrict s, f x ≤ c) :
    (μ.withDensity f).restrict s ≤ c • μ := by
  have hlocal :
      (μ.withDensity f).restrict s ≤ c • μ.restrict s :=
    restrict_withDensity_le_smul_restrict_of_ae_le hs hf
  exact measure_le_smul_of_le_smul_restrict (μ := μ) (U := s) hlocal

/-- If an unweighted local source measure is dominated by a scalar multiple
of a reference measure, then adding a locally bounded prior density preserves
domination with the multiplied scalar.

This is the source-prior adapter: it separates the remaining Haar/chart
transport problem (`μ.restrict s ≤ c • ν`) from the elementary bounded-prior
bookkeeping.  Finiteness of `C` and `c`, when needed for later integrability
transfer, is a downstream hypothesis. -/
theorem restrict_withDensity_le_smul_of_restrict_le_smul_of_ae_le
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {f : α → ℝ≥0∞}
    {s : Set α} {C c : ℝ≥0∞}
    (hs : MeasurableSet s)
    (hμ : μ.restrict s ≤ c • ν)
    (hf : ∀ᵐ x ∂μ.restrict s, f x ≤ C) :
    (μ.withDensity f).restrict s ≤ (C * c) • ν := by
  have hlocal :
      (μ.withDensity f).restrict s ≤ C • μ.restrict s :=
    restrict_withDensity_le_smul_restrict_of_ae_le hs hf
  have hscale : C • μ.restrict s ≤ C • (c • ν) := by
    refine Measure.le_iff.2 ?_
    intro t _ht
    rw [Measure.smul_apply, Measure.smul_apply]
    exact mul_le_mul_right (hμ t) C
  have hsmul_assoc : C • (c • ν) = (C * c) • ν := by
    ext t ht
    simp [Measure.smul_apply, mul_assoc]
  calc
    (μ.withDensity f).restrict s ≤ C • μ.restrict s := hlocal
    _ ≤ C • (c • ν) := hscale
    _ = (C * c) • ν := hsmul_assoc

/-- Two successive locally bounded density perturbations preserve scalar
domination of a restricted base measure.

The second density is bounded almost everywhere for the once-weighted
restricted measure, which is the measure against which that density is applied. -/
theorem restrict_two_withDensity_le_smul_of_restrict_le_smul_of_ae_le
    {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {J S : α → ℝ≥0∞} {V : Set α}
    {Cbase CJ CS : ℝ≥0∞}
    (hV : MeasurableSet V)
    (hbase : μ.restrict V ≤ Cbase • ν)
    (hJ : ∀ᵐ z ∂μ.restrict V, J z ≤ CJ)
    (hS : ∀ᵐ z ∂(μ.withDensity J).restrict V, S z ≤ CS) :
    ((μ.withDensity J).withDensity S).restrict V ≤
      (CS * (CJ * Cbase)) • ν := by
  have hJdom :
      (μ.withDensity J).restrict V ≤ (CJ * Cbase) • ν :=
    restrict_withDensity_le_smul_of_restrict_le_smul_of_ae_le
      (μ := μ) (ν := ν) (f := J) hV hbase hJ
  exact
    restrict_withDensity_le_smul_of_restrict_le_smul_of_ae_le
      (μ := μ.withDensity J) (ν := ν) (f := S) hV hJdom hS

/-- Finite-scalar version of
`restrict_two_withDensity_le_smul_of_restrict_le_smul_of_ae_le`. -/
theorem restrict_two_withDensity_le_smul_of_restrict_le_smul_of_ae_le_of_lt_top
    {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {J S : α → ℝ≥0∞} {V : Set α}
    {Cbase CJ CS : ℝ≥0∞}
    (hV : MeasurableSet V)
    (hbase : μ.restrict V ≤ Cbase • ν)
    (hJ : ∀ᵐ z ∂μ.restrict V, J z ≤ CJ)
    (hS : ∀ᵐ z ∂(μ.withDensity J).restrict V, S z ≤ CS)
    (hCbase : Cbase < ∞) (hCJ : CJ < ∞) (hCS : CS < ∞) :
    (CS * (CJ * Cbase)) < ∞ ∧
      ((μ.withDensity J).withDensity S).restrict V ≤
        (CS * (CJ * Cbase)) • ν :=
  ⟨ENNReal.mul_lt_top hCS (ENNReal.mul_lt_top hCJ hCbase),
    restrict_two_withDensity_le_smul_of_restrict_le_smul_of_ae_le
      hV hbase hJ hS⟩

/-- Real-valued version of
`restrict_withDensity_le_smul_of_restrict_le_smul_of_ae_le`, for priors
written as `ENNReal.ofReal` of a locally bounded real density. -/
theorem restrict_withDensity_ofReal_le_smul_of_restrict_le_smul_of_ae_le
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {density : α → ℝ}
    {s : Set α} {K : ℝ} {c : ℝ≥0∞}
    (hs : MeasurableSet s)
    (hμ : μ.restrict s ≤ c • ν)
    (hdensity : ∀ᵐ x ∂μ.restrict s, density x ≤ K) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (density x))).restrict s ≤
      (ENNReal.ofReal K * c) • ν :=
  restrict_withDensity_le_smul_of_restrict_le_smul_of_ae_le
    (μ := μ) (ν := ν)
    (f := fun x ↦ ENNReal.ofReal (density x)) hs hμ
    (hdensity.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx)

end Aoyagi
end DLN
end DLNFibre

end
