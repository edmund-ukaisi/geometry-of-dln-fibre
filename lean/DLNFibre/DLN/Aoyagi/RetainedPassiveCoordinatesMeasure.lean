import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Measure bridge for retained-passive raw-order coordinates

This file packages the retained-passive raw-order determinant-chart
differentiability and injectivity facts in the form expected by Mathlib's
finite-dimensional Jacobian change-of-variables theorem.

The main results are local weighted and inverse-density pushforward identities
on the tuple determinant chart.  The file also constructs the pointwise
chart-side inverse Jacobian density and proves the continuity/a.e.-
measurability inputs needed for the inverse-density pushforward form.

It does not compute an explicit determinant formula, identify source/prior
densities, prove normal crossings, compute a pole order, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix.Norms.Operator Topology

namespace DLNFibre
namespace DLN
namespace Aoyagi
namespace ChartLocalSuffixState
namespace RetainedPassiveNonredundantCoordinateData

private theorem map_withDensity_comp_of_aemeasurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {η : Measure α} {f : α → β} {g : β → ℝ≥0∞}
    (hf : AEMeasurable f η)
    (hg : AEMeasurable g (Measure.map f η)) :
    Measure.map f (η.withDensity (fun x => g (f x))) =
      (Measure.map f η).withDensity g := by
  ext t ht
  have hf_density :
      AEMeasurable f (η.withDensity (fun x => g (f x))) :=
    hf.mono_ac (withDensity_absolutelyContinuous _ _)
  have hpre : NullMeasurableSet (f ⁻¹' t) η :=
    hf.nullMeasurableSet_preimage ht
  rw [Measure.map_apply_of_aemeasurable hf_density ht,
    withDensity_apply _ ht,
    withDensity_apply₀ _ hpre]
  calc
    ∫⁻ x in f ⁻¹' t, g (f x) ∂η =
        ∫⁻ x, (f ⁻¹' t).indicator (fun x => g (f x)) x ∂η := by
          rw [lintegral_indicator₀ hpre]
    _ = ∫⁻ x, (t.indicator g) (f x) ∂η := by
          rfl
    _ = ∫⁻ y, t.indicator g y ∂Measure.map f η := by
          exact (lintegral_map' (hg.indicator ht) hf).symm
    _ = ∫⁻ y in t, g y ∂Measure.map f η := by
          rw [lintegral_indicator ht]

/-- The retained-passive tuple determinant chart is null-measurable for any
Borel-space measure. -/
theorem nullMeasurableSet_topologyTupleDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ)) :
    NullMeasurableSet
      (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m :=
  (isOpen_topologyTupleDetChartSet
    (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet.nullMeasurableSet

/-- The raw-order target source-recursive determinant chart is
null-measurable for any Borel-space measure. -/
theorem nullMeasurableSet_topologyTupleRawOrderSourceRecursiveDetChartSet
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ)) :
    NullMeasurableSet
      (topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) m :=
  (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
    (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet.nullMeasurableSet

/-- The target-side inverse determinant density associated to the retained-
passive raw-order coordinate change.  For raw-order target variables `y`, this
is `|det Df(f⁻¹ y)|⁻¹`, not the source-side forward density. -/
def topologyTupleEdgeRawOrderInverseJacobianDensity
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (y : TopologyTuple ρ κ' ℝ) : ℝ :=
  (topologyTupleEdgeRawOrderFDerivAbsDet
    (ρ := ρ) (κ' := κ')
    (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y))⁻¹

/-- On the retained-passive tuple determinant chart, the target-side inverse
density evaluated at the raw-order image is the reciprocal of the source-side
forward Jacobian density. -/
theorem topologyTupleEdgeRawOrderInverseJacobianDensity_apply_chartMap
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    topologyTupleEdgeRawOrderInverseJacobianDensity
        (ρ := ρ) (κ' := κ')
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z) =
      (topologyTupleEdgeRawOrderFDerivAbsDet
        (ρ := ρ) (κ' := κ') z)⁻¹ := by
  rw [topologyTupleEdgeRawOrderInverseJacobianDensity]
  rw [topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
    (K := ℝ) (ρ := ρ) (κ' := κ') hz]

/-- On the retained-passive tuple determinant chart, the source-side forward
Jacobian density cancels the target-side inverse density after applying the
raw-order map. -/
theorem topologyTupleEdgeRawOrderFDerivAbsDet_mul_inverseJacobianDensity_apply_chartMap
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {z : TopologyTuple ρ κ' ℝ}
    (hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z) *
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderInverseJacobianDensity
          (ρ := ρ) (κ' := κ')
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)) =
        1 := by
  have hpos :
      0 < topologyTupleEdgeRawOrderFDerivAbsDet
        (ρ := ρ) (κ' := κ') z :=
    topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') hz
  rw [topologyTupleEdgeRawOrderInverseJacobianDensity_apply_chartMap
      (ρ := ρ) (κ' := κ') hz,
    ENNReal.ofReal_inv_of_pos hpos]
  exact ENNReal.mul_inv_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr hpos))
    (by simp)

/-- The target-side inverse determinant density is positive at points of the
raw-order source-recursive determinant chart. -/
theorem topologyTupleEdgeRawOrderInverseJacobianDensity_pos_of_mem_rawSourceChart
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {y : TopologyTuple ρ κ' ℝ}
    (hy : y ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) :
    0 < topologyTupleEdgeRawOrderInverseJacobianDensity
      (ρ := ρ) (κ' := κ') y := by
  have hpre :
      topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y ∈
        topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') :=
    topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ') hy
  have hpos :
      0 < topologyTupleEdgeRawOrderFDerivAbsDet
        (ρ := ρ) (κ' := κ')
        (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y) :=
    topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') hpre
  simpa [topologyTupleEdgeRawOrderInverseJacobianDensity] using
    inv_pos.mpr hpos

/-- The target-side inverse determinant density is continuous at points of the
raw-order source-recursive determinant chart. -/
theorem continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (y₀ : TopologyTuple ρ κ' ℝ)
    (hy₀ : y₀ ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ContinuousAt
      (topologyTupleEdgeRawOrderInverseJacobianDensity
        (ρ := ρ) (κ' := κ')) y₀ := by
  let invMap : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ')
  have hpre :
      invMap y₀ ∈ topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') :=
    topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ') hy₀
  have hinv : ContinuousAt invMap y₀ :=
    continuousAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ') hy₀
  have hforward :
      ContinuousAt
        (fun y : TopologyTuple ρ κ' ℝ =>
          topologyTupleEdgeRawOrderFDerivAbsDet
            (ρ := ρ) (κ' := κ') (invMap y)) y₀ :=
    (continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') (invMap y₀) hpre).comp hinv
  have hpos :
      0 < topologyTupleEdgeRawOrderFDerivAbsDet
        (ρ := ρ) (κ' := κ') (invMap y₀) :=
    topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') hpre
  simpa [topologyTupleEdgeRawOrderInverseJacobianDensity, invMap] using
    (ContinuousAt.inv₀ hforward (ne_of_gt hpos))

/-- Composing a continuous target chart tuple with the target-side inverse
Jacobian density preserves continuity at raw-order source-recursive
determinant-chart points. -/
theorem continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_comp_of_mem_rawSourceChart
    {M : ℕ} {ρ α : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [TopologicalSpace α]
    {Y : α → TopologyTuple ρ κ' ℝ} {a₀ : α}
    (hY : ContinuousAt Y a₀)
    (hY₀ : Y a₀ ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ContinuousAt
      (fun a : α =>
        topologyTupleEdgeRawOrderInverseJacobianDensity
          (ρ := ρ) (κ' := κ') (Y a)) a₀ :=
  (continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart
    (ρ := ρ) (κ' := κ') (Y a₀) hY₀).comp hY

/-- Composing any target chart tuple with the target-side inverse determinant
density is positive at raw-order source-recursive determinant-chart points. -/
theorem topologyTupleEdgeRawOrderInverseJacobianDensity_comp_pos_of_mem_rawSourceChart
    {M : ℕ} {ρ α : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (Y : α → TopologyTuple ρ κ' ℝ) (a₀ : α)
    (hY₀ : Y a₀ ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) :
    0 <
      topologyTupleEdgeRawOrderInverseJacobianDensity
        (ρ := ρ) (κ' := κ') (Y a₀) :=
  topologyTupleEdgeRawOrderInverseJacobianDensity_pos_of_mem_rawSourceChart
    (ρ := ρ) (κ' := κ') hY₀

/-- Near any raw-order source-recursive determinant-chart point, the
target-side inverse Jacobian density admits a positive lower bound. -/
theorem exists_pos_eventually_le_topologyTupleEdgeRawOrderInverseJacobianDensity_nhds
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (y₀ : TopologyTuple ρ κ' ℝ)
    (hy₀ : y₀ ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ y in 𝓝 y₀,
        ε ≤ topologyTupleEdgeRawOrderInverseJacobianDensity
          (ρ := ρ) (κ' := κ') y := by
  let density : TopologyTuple ρ κ' ℝ → ℝ :=
    topologyTupleEdgeRawOrderInverseJacobianDensity
      (ρ := ρ) (κ' := κ')
  have hdensity : ContinuousAt density y₀ :=
    continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart
      (ρ := ρ) (κ' := κ') y₀ hy₀
  have hpos : 0 < density y₀ :=
    topologyTupleEdgeRawOrderInverseJacobianDensity_pos_of_mem_rawSourceChart
      (ρ := ρ) (κ' := κ') hy₀
  refine ⟨density y₀ / 2, half_pos hpos, ?_⟩
  have htarget : ∀ᶠ y in 𝓝 (density y₀), density y₀ / 2 ≤ y := by
    exact eventually_ge_nhds (show density y₀ / 2 < density y₀ by linarith)
  exact hdensity.eventually htarget

/-- Near any raw-order source-recursive determinant-chart point, the
target-side inverse Jacobian density admits a positive upper bound. -/
theorem exists_pos_eventually_topologyTupleEdgeRawOrderInverseJacobianDensity_le_nhds
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (y₀ : TopologyTuple ρ κ' ℝ)
    (hy₀ : y₀ ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ y in 𝓝 y₀,
        topologyTupleEdgeRawOrderInverseJacobianDensity
          (ρ := ρ) (κ' := κ') y ≤ C := by
  let density : TopologyTuple ρ κ' ℝ → ℝ :=
    topologyTupleEdgeRawOrderInverseJacobianDensity
      (ρ := ρ) (κ' := κ')
  have hdensity : ContinuousAt density y₀ :=
    continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart
      (ρ := ρ) (κ' := κ') y₀ hy₀
  refine ⟨max (density y₀ + 1) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · have htarget : ∀ᶠ y in 𝓝 (density y₀), y ≤ density y₀ + 1 := by
      exact eventually_le_nhds (show density y₀ < density y₀ + 1 by linarith)
    exact (hdensity.eventually htarget).mono
      (fun _ hy ↦ hy.trans (le_max_left _ _))

/-- The retained-passive target-side inverse Jacobian density is a positive
bounded unit after any source parametrization continuous at a point mapping
into the raw-order source-recursive determinant chart. -/
theorem exists_pos_eventually_bounds_topologyTupleEdgeRawOrderInverseJacobianDensity_comp
    {α : Type*} [TopologicalSpace α]
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {Y : α → TopologyTuple ρ κ' ℝ} {a₀ : α}
    (hY : ContinuousAt Y a₀)
    (hY₀ : Y a₀ ∈ topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ᶠ a in 𝓝 a₀,
        ε ≤ topologyTupleEdgeRawOrderInverseJacobianDensity
            (ρ := ρ) (κ' := κ') (Y a) ∧
          topologyTupleEdgeRawOrderInverseJacobianDensity
            (ρ := ρ) (κ' := κ') (Y a) ≤ C := by
  rcases exists_pos_eventually_le_topologyTupleEdgeRawOrderInverseJacobianDensity_nhds
      (ρ := ρ) (κ' := κ') (Y a₀) hY₀ with
    ⟨ε, hε_pos, hε⟩
  rcases exists_pos_eventually_topologyTupleEdgeRawOrderInverseJacobianDensity_le_nhds
      (ρ := ρ) (κ' := κ') (Y a₀) hY₀ with
    ⟨C, hC_pos, hC⟩
  refine ⟨ε, C, hε_pos, hC_pos, ?_⟩
  filter_upwards [hY.eventually hε, hY.eventually hC] with a ha_low ha_high
  exact ⟨ha_low, ha_high⟩

set_option maxRecDepth 2048 in
/-- On the retained-passive tuple determinant chart, the raw-order chart map
pushes the weighted source Haar measure with density `|det Df|` to Haar measure
restricted to the image. -/
theorem map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (topologyTupleEdgeRawOrderFDerivAbsDet
                (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') ''
          topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) := by
  have hf' :
      ∀ z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'),
        HasFDerivWithinAt
          (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
          (fderiv ℝ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z)
          (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) z := by
    intro z hz
    exact
      (differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') z hz).hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn
      (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
      (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :=
    injOn_topologyTupleEdgeRawOrder_detChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  simpa [topologyTupleEdgeRawOrderFDerivAbsDet] using
    MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
      (μ := m)
      (f := topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
      (f' := fun z : TopologyTuple ρ κ' ℝ =>
        fderiv ℝ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')) z)
      hs hf' hinj

set_option maxRecDepth 2048 in
/-- On the retained-passive tuple determinant chart, the raw-order chart map
pushes the weighted source Haar measure with density `|det Df|` to Haar measure
restricted to the raw-order source-recursive determinant chart. -/
theorem map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (topologyTupleEdgeRawOrderFDerivAbsDet
                (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')) := by
  simpa [image_topologyTupleEdgeRawOrder_detChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')] using
    map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det
      (ρ := ρ) (κ' := κ') m hs

set_option maxRecDepth 2048 in
/-- Borel-space convenience wrapper for the retained-passive raw-order weighted
change-of-variables identity with image target. -/
theorem map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det'
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure] :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (topologyTupleEdgeRawOrderFDerivAbsDet
                (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') ''
          topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) :=
  map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det
    (ρ := ρ) (κ' := κ') m
    (nullMeasurableSet_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') m)

set_option maxRecDepth 2048 in
/-- Borel-space convenience wrapper for the retained-passive raw-order weighted
change-of-variables identity with the named raw source-recursive target chart. -/
theorem map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart'
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure] :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (topologyTupleEdgeRawOrderFDerivAbsDet
                (ρ := ρ) (κ' := κ') z))) =
      m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')) :=
  map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
    (ρ := ρ) (κ' := κ') m
    (nullMeasurableSet_topologyTupleDetChartSet
      (ρ := ρ) (κ' := κ') m)

set_option maxRecDepth 2048 in
/-- Conditional inverse-density form of the retained-passive raw-order
change-of-variables theorem, with the density a.e.-measurability hypotheses
kept explicit for downstream consumers that already have them in hand. -/
theorem
    map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian_of_aemeasurable
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m)
    (hF :
      AEMeasurable
        (fun z : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderFDerivAbsDet
              (ρ := ρ) (κ' := κ') z))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))))
    (hG :
      AEMeasurable
        (fun y : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderInverseJacobianDensity
              (ρ := ρ) (κ' := κ') y))
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))))
    (hG_comp :
      AEMeasurable
        (fun z : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderInverseJacobianDensity
              (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')))) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))) =
      (m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
        (fun y : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderInverseJacobianDensity
              (ρ := ρ) (κ' := κ') y)) := by
  classical
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let F : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z)
  let G : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderInverseJacobianDensity
          (ρ := ρ) (κ' := κ') y)
  have hΦ_contOn : ContinuousOn Φ S := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun z :
          topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ_μs : AEMeasurable Φ (m.restrict S) :=
    ContinuousOn.aemeasurable₀ hΦ_contOn (by simpa [S] using hs)
  have hF_μs : AEMeasurable F (m.restrict S) := by
    simpa [F, S] using hF
  have hG_μt : AEMeasurable G (m.restrict T) := by
    simpa [G, T] using hG
  have hG_comp_μs : AEMeasurable (fun z => G (Φ z)) (m.restrict S) := by
    simpa [G, Φ, S] using hG_comp
  have hcov :
      Measure.map Φ ((m.restrict S).withDensity F) =
        m.restrict T := by
    simpa [Φ, F, S, T] using
      map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
        (ρ := ρ) (κ' := κ') m hs
  have hΦ_weighted :
      AEMeasurable Φ ((m.restrict S).withDensity F) :=
    hΦ_μs.mono_ac (withDensity_absolutelyContinuous _ _)
  have hG_map :
      AEMeasurable G
        (Measure.map Φ ((m.restrict S).withDensity F)) := by
    rw [hcov]
    exact hG_μt
  have htransport :
      Measure.map Φ
          (((m.restrict S).withDensity F).withDensity
            (fun z => G (Φ z))) =
        (Measure.map Φ ((m.restrict S).withDensity F)).withDensity G :=
    map_withDensity_comp_of_aemeasurable hΦ_weighted hG_map
  have hcancel :
      (F * fun z => G (Φ z)) =ᵐ[m.restrict S] 1 := by
    filter_upwards [ae_restrict_mem₀ (by simpa [S] using hs)] with z hz
    simpa [F, G, Φ, S] using
      topologyTupleEdgeRawOrderFDerivAbsDet_mul_inverseJacobianDensity_apply_chartMap
        (ρ := ρ) (κ' := κ') hz
  symm
  calc
    (m.restrict T).withDensity G =
        (Measure.map Φ ((m.restrict S).withDensity F)).withDensity G := by
          rw [hcov]
    _ =
        Measure.map Φ
          (((m.restrict S).withDensity F).withDensity
            (fun z => G (Φ z))) := htransport.symm
    _ =
        Measure.map Φ
          ((m.restrict S).withDensity (F * fun z => G (Φ z))) := by
          rw [← withDensity_mul₀ hF_μs hG_comp_μs]
    _ =
        Measure.map Φ ((m.restrict S).withDensity 1) := by
          rw [withDensity_congr_ae hcancel]
    _ =
        Measure.map Φ (m.restrict S) := by
          rw [withDensity_one]

set_option maxRecDepth 2048 in
/-- Inverse-density form of the retained-passive raw-order change-of-variables
theorem.  The density a.e.-measurability hypotheses are discharged from the
retained-passive `C^1` forward-density continuity and the topological inverse
on the raw-order target chart. -/
theorem map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m) :
    Measure.map
        (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ'))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))) =
      (m.restrict
        (topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
        (fun y : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderInverseJacobianDensity
              (ρ := ρ) (κ' := κ') y)) := by
  classical
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let F : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z)
  let G : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderInverseJacobianDensity
          (ρ := ρ) (κ' := κ') y)
  have hT :
      NullMeasurableSet T m := by
    simpa [T] using
      nullMeasurableSet_topologyTupleRawOrderSourceRecursiveDetChartSet
        (ρ := ρ) (κ' := κ') m
  have hΦ_contOn : ContinuousOn Φ S := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun z :
          topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hF :
      AEMeasurable F (m.restrict S) := by
    refine ContinuousOn.aemeasurable₀ ?_ (by simpa [S] using hs)
    intro z hz
    exact
      (ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
          (ρ := ρ) (κ' := κ') z hz)).continuousWithinAt
  have hG :
      AEMeasurable G (m.restrict T) := by
    refine ContinuousOn.aemeasurable₀ ?_ hT
    intro y hy
    exact
      (ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart
          (ρ := ρ) (κ' := κ') y hy)).continuousWithinAt
  have hG_comp :
      AEMeasurable (fun z => G (Φ z)) (m.restrict S) := by
    refine ContinuousOn.aemeasurable₀ ?_ (by simpa [S] using hs)
    intro z hz
    have hΦz : Φ z ∈ T := by
      simpa [Φ, T] using
        mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ') hz
    have hGcont : ContinuousAt G (Φ z) :=
      ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart
          (ρ := ρ) (κ' := κ') (Φ z) hΦz)
    exact hGcont.comp_continuousWithinAt (hΦ_contOn z hz)
  simpa [S, T, Φ, F, G] using
    map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian_of_aemeasurable
      (ρ := ρ) (κ' := κ') m hs hF hG hG_comp

set_option maxRecDepth 2048 in
/-- The retained-passive weighted raw-order change-of-variables theorem
composed with an arbitrary a.e.-measurable target map. -/
theorem
    map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_eq_map_restrict_rawSourceChart
    {M : ℕ} {ρ β : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace β]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (ψ : TopologyTuple ρ κ' ℝ → β)
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m)
    (hψ :
      AEMeasurable ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))) :
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ =>
          ψ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (topologyTupleEdgeRawOrderFDerivAbsDet
                (ρ := ρ) (κ' := κ') z))) =
      Measure.map ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))) := by
  classical
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let F : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderFDerivAbsDet
          (ρ := ρ) (κ' := κ') z)
  let μ : Measure (TopologyTuple ρ κ' ℝ) :=
    (m.restrict S).withDensity F
  have hΦ_contOn : ContinuousOn Φ S := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun z :
          topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ_restrict : AEMeasurable Φ (m.restrict S) :=
    ContinuousOn.aemeasurable₀ hΦ_contOn (by simpa [S] using hs)
  have hΦ_μ : AEMeasurable Φ μ := by
    simpa [μ] using hΦ_restrict.mono_ac (withDensity_absolutelyContinuous _ _)
  have hcov :
      Measure.map Φ μ = m.restrict T := by
    simpa [Φ, F, μ, S, T] using
      map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
        (ρ := ρ) (κ' := κ') m hs
  have hψ_map : AEMeasurable ψ (Measure.map Φ μ) := by
    rw [hcov]
    simpa [T] using hψ
  calc
    Measure.map (fun z : TopologyTuple ρ κ' ℝ => ψ (Φ z)) μ =
        Measure.map ψ (Measure.map Φ μ) := by
          simpa [Function.comp_def] using
            (AEMeasurable.map_map_of_aemeasurable
              (μ := μ) (g := ψ) (f := Φ) hψ_map hΦ_μ).symm
    _ =
        Measure.map ψ (m.restrict T) := by
          rw [hcov]

set_option maxRecDepth 2048 in
/-- The retained-passive weighted raw-order change-of-variables theorem read
through the raw-order edge-family decoder. -/
theorem
    map_topologyTupleEdgeMatrix_withDensity_absDet_eq_map_edgeFamilyOfRawOrderTuple
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace (EdgeFamilyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m)
    (hread :
      AEMeasurable
        (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))) :
    Measure.map
        (topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun z : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (topologyTupleEdgeRawOrderFDerivAbsDet
                (ρ := ρ) (κ' := κ') z))) =
      Measure.map
        (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))) := by
  let μ : Measure (TopologyTuple ρ κ' ℝ) :=
    (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
      (fun z : TopologyTuple ρ κ' ℝ =>
        ENNReal.ofReal
          (topologyTupleEdgeRawOrderFDerivAbsDet
            (ρ := ρ) (κ' := κ') z))
  have hgeneric :
      Measure.map
          (fun z : TopologyTuple ρ κ' ℝ =>
            edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          μ =
        Measure.map
          (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
          (m.restrict
            (topologyTupleRawOrderSourceRecursiveDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ'))) := by
    simpa [μ] using
      map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_eq_map_restrict_rawSourceChart
        (ρ := ρ) (κ' := κ')
        (β := EdgeFamilyTuple ρ κ' ℝ)
        m (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ')) hs hread
  have hmap :
      Measure.map
          (topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ')) μ =
        Measure.map
          (fun z : TopologyTuple ρ κ' ℝ =>
            edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          μ := by
    refine Measure.map_congr ?_
    filter_upwards with z
    exact
      (edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := ρ) (κ' := κ') z).symm
  rw [hmap]
  exact hgeneric

set_option maxRecDepth 2048 in
/-- The conditional inverse-density retained-passive raw-order change of
variables theorem composed with an arbitrary downstream map. -/
theorem
    map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac_of_aemeasurable
    {M : ℕ} {ρ β : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace β]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (ψ : TopologyTuple ρ κ' ℝ → β)
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m)
    (hF :
      AEMeasurable
        (fun z : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderFDerivAbsDet
              (ρ := ρ) (κ' := κ') z))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))))
    (hG :
      AEMeasurable
        (fun y : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderInverseJacobianDensity
              (ρ := ρ) (κ' := κ') y))
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))))
    (hG_comp :
      AEMeasurable
        (fun z : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderInverseJacobianDensity
              (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))))
    (hψ :
      AEMeasurable ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))) :
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ =>
          ψ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))) =
      Measure.map ψ
        ((m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun y : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (topologyTupleEdgeRawOrderInverseJacobianDensity
                (ρ := ρ) (κ' := κ') y))) := by
  classical
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let G : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderInverseJacobianDensity
          (ρ := ρ) (κ' := κ') y)
  have hΦ_contOn : ContinuousOn Φ S := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun z :
          topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ : AEMeasurable Φ (m.restrict S) :=
    ContinuousOn.aemeasurable₀ hΦ_contOn (by simpa [S] using hs)
  have hpush :
      Measure.map Φ (m.restrict S) =
        (m.restrict T).withDensity G := by
    simpa [Φ, G, S, T] using
      map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian_of_aemeasurable
        (ρ := ρ) (κ' := κ') m hs hF hG hG_comp
  have hψ_T : AEMeasurable ψ (m.restrict T) := by
    simpa [T] using hψ
  have hψ_target : AEMeasurable ψ ((m.restrict T).withDensity G) :=
    hψ_T.mono_ac (withDensity_absolutelyContinuous _ _)
  have hψ_map : AEMeasurable ψ (Measure.map Φ (m.restrict S)) := by
    rw [hpush]
    exact hψ_target
  calc
    Measure.map (fun z : TopologyTuple ρ κ' ℝ => ψ (Φ z)) (m.restrict S) =
        Measure.map ψ (Measure.map Φ (m.restrict S)) := by
          simpa [Function.comp_def] using
            (AEMeasurable.map_map_of_aemeasurable
              (μ := m.restrict S) (g := ψ) (f := Φ)
              hψ_map hΦ).symm
    _ =
        Measure.map ψ ((m.restrict T).withDensity G) := by
          rw [hpush]

set_option maxRecDepth 2048 in
/-- The inverse-density retained-passive raw-order change-of-variables theorem
composed with an arbitrary downstream map. -/
theorem map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac
    {M : ℕ} {ρ β : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace β]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (ψ : TopologyTuple ρ κ' ℝ → β)
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m)
    (hψ :
      AEMeasurable ψ
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))) :
    Measure.map
        (fun z : TopologyTuple ρ κ' ℝ =>
          ψ (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))) =
      Measure.map ψ
        ((m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun y : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (topologyTupleEdgeRawOrderInverseJacobianDensity
                (ρ := ρ) (κ' := κ') y))) := by
  classical
  let S : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let T : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleRawOrderSourceRecursiveDetChartSet
      (K := ℝ) (ρ := ρ) (κ' := κ')
  let Φ : TopologyTuple ρ κ' ℝ → TopologyTuple ρ κ' ℝ :=
    topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ')
  let G : TopologyTuple ρ κ' ℝ → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
        (topologyTupleEdgeRawOrderInverseJacobianDensity
          (ρ := ρ) (κ' := κ') y)
  have hΦ_contOn : ContinuousOn Φ S := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun z :
          topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') =>
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hΦ : AEMeasurable Φ (m.restrict S) :=
    ContinuousOn.aemeasurable₀ hΦ_contOn (by simpa [S] using hs)
  have hpush :
      Measure.map Φ (m.restrict S) =
        (m.restrict T).withDensity G := by
    simpa [Φ, G, S, T] using
      map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian
        (ρ := ρ) (κ' := κ') m hs
  have hψ_T : AEMeasurable ψ (m.restrict T) := by
    simpa [T] using hψ
  have hψ_target : AEMeasurable ψ ((m.restrict T).withDensity G) :=
    hψ_T.mono_ac (withDensity_absolutelyContinuous _ _)
  have hψ_map : AEMeasurable ψ (Measure.map Φ (m.restrict S)) := by
    rw [hpush]
    exact hψ_target
  calc
    Measure.map (fun z : TopologyTuple ρ κ' ℝ => ψ (Φ z)) (m.restrict S) =
        Measure.map ψ (Measure.map Φ (m.restrict S)) := by
          simpa [Function.comp_def] using
            (AEMeasurable.map_map_of_aemeasurable
              (μ := m.restrict S) (g := ψ) (f := Φ)
              hψ_map hΦ).symm
    _ =
        Measure.map ψ ((m.restrict T).withDensity G) := by
          rw [hpush]

set_option maxRecDepth 2048 in
/-- The conditional inverse-density retained-passive raw-order change of
variables theorem read through the raw-order edge-family decoder. -/
theorem
    map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac_of_aemeasurable
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace (EdgeFamilyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m)
    (hF :
      AEMeasurable
        (fun z : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderFDerivAbsDet
              (ρ := ρ) (κ' := κ') z))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))))
    (hG :
      AEMeasurable
        (fun y : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderInverseJacobianDensity
              (ρ := ρ) (κ' := κ') y))
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))))
    (hG_comp :
      AEMeasurable
        (fun z : TopologyTuple ρ κ' ℝ =>
          ENNReal.ofReal
            (topologyTupleEdgeRawOrderInverseJacobianDensity
              (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z)))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))))
    (hread :
      AEMeasurable
        (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))) :
    Measure.map
        (topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ'))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))) =
      Measure.map
        (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun y : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (topologyTupleEdgeRawOrderInverseJacobianDensity
                (ρ := ρ) (κ' := κ') y))) := by
  let μ : Measure (TopologyTuple ρ κ' ℝ) :=
    m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
  have hgeneric :
      Measure.map
          (fun z : TopologyTuple ρ κ' ℝ =>
            edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          μ =
        Measure.map
          (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
          ((m.restrict
            (topologyTupleRawOrderSourceRecursiveDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
            (fun y : TopologyTuple ρ κ' ℝ =>
              ENNReal.ofReal
                (topologyTupleEdgeRawOrderInverseJacobianDensity
                  (ρ := ρ) (κ' := κ') y))) := by
    simpa [μ] using
      map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac_of_aemeasurable
        (ρ := ρ) (κ' := κ')
        (β := EdgeFamilyTuple ρ κ' ℝ)
        m (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
        hs hF hG hG_comp hread
  have hmap :
      Measure.map
          (topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ')) μ =
        Measure.map
          (fun z : TopologyTuple ρ κ' ℝ =>
            edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          μ := by
    refine Measure.map_congr ?_
    filter_upwards with z
    exact
      (edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := ρ) (κ' := κ') z).symm
  rw [hmap]
  exact hgeneric

set_option maxRecDepth 2048 in
/-- The inverse-density retained-passive raw-order change-of-variables theorem
read through the raw-order edge-family decoder. -/
theorem map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac
    {M : ℕ} {ρ : Type*} {κ' : Fin (M + 2) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [MeasurableSpace (EdgeFamilyTuple ρ κ' ℝ)]
    (m : Measure (TopologyTuple ρ κ' ℝ))
    [m.IsAddHaarMeasure]
    (hs :
      NullMeasurableSet
        (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')) m)
    (hread :
      AEMeasurable
        (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
        (m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')))) :
    Measure.map
        (topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ'))
        (m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))) =
      Measure.map
        (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
        ((m.restrict
          (topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
          (fun y : TopologyTuple ρ κ' ℝ =>
            ENNReal.ofReal
              (topologyTupleEdgeRawOrderInverseJacobianDensity
                (ρ := ρ) (κ' := κ') y))) := by
  let μ : Measure (TopologyTuple ρ κ' ℝ) :=
    m.restrict (topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
  have hgeneric :
      Measure.map
          (fun z : TopologyTuple ρ κ' ℝ =>
            edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          μ =
        Measure.map
          (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
          ((m.restrict
            (topologyTupleRawOrderSourceRecursiveDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ'))).withDensity
            (fun y : TopologyTuple ρ κ' ℝ =>
              ENNReal.ofReal
                (topologyTupleEdgeRawOrderInverseJacobianDensity
                  (ρ := ρ) (κ' := κ') y))) := by
    simpa [μ] using
      map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac
        (ρ := ρ) (κ' := κ')
        (β := EdgeFamilyTuple ρ κ' ℝ)
        m (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
        hs hread
  have hmap :
      Measure.map
          (topologyTupleEdgeMatrix (K := ℝ) (ρ := ρ) (κ' := κ')) μ =
        Measure.map
          (fun z : TopologyTuple ρ κ' ℝ =>
            edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') z))
          μ := by
    refine Measure.map_congr ?_
    filter_upwards with z
    exact
      (edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := ρ) (κ' := κ') z).symm
  rw [hmap]
  exact hgeneric

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
