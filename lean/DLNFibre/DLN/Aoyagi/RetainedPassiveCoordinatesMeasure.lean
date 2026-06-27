import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Measure bridge for retained-passive raw-order coordinates

This file packages the retained-passive raw-order determinant-chart
differentiability and injectivity facts in the form expected by Mathlib's
finite-dimensional Jacobian change-of-variables theorem.

The result is a local weighted pushforward identity on the tuple determinant
chart.  It does not compute an explicit determinant formula, construct an
inverse Jacobian density, identify source/prior densities, prove normal
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

end RetainedPassiveNonredundantCoordinateData
end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
