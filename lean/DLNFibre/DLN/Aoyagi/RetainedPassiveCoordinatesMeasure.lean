import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Measure bridge for retained-passive raw-order coordinates

This file packages the retained-passive raw-order determinant-chart
differentiability and injectivity facts in the form expected by Mathlib's
finite-dimensional Jacobian change-of-variables theorem.

The main result is a local weighted pushforward identity on the tuple
determinant chart.  The file also constructs the pointwise chart-side inverse
Jacobian density and proves the inverse-density pushforward form under explicit
a.e.-measurability hypotheses.

It does not compute an explicit determinant formula, prove determinant-density
continuity or measurability, identify source/prior densities, prove normal
crossings, compute a pole order, or extract an RLCT.
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
change-of-variables theorem.  The a.e.-measurability hypotheses are explicit
because this file does not prove continuity of the retained-passive determinant
density. -/
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

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
