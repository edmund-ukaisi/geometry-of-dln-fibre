import DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Measure bridge for Aoyagi's p. 13 product-step coordinate change

This file packages the product-step determinant-chart derivative and
injectivity facts in the form expected by Mathlib's finite-dimensional
Jacobian change-of-variables theorem.

The result is only a local weighted pushforward identity on the raw
determinant-chart set. It does not identify the image with the full target
determinant chart, prove source coverage, produce normal crossings, compute a
pole order, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix.Norms.Operator

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Raw tuple space for the p. 13 product-step coordinate change over `ℝ`. -/
abbrev ProductReductionStepRawTopologyTuple (ρ π μ ν : Type*) :=
  ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ

/-- The raw determinant-chart set for the p. 13 product-step coordinate
change. -/
def productReductionStepRawDetChartSet
    (ρ π μ ν : Type*) [Fintype ρ] [DecidableEq ρ] :
    Set (ProductReductionStepRawTopologyTuple ρ π μ ν) :=
  {z | IsUnit z.1.det ∧ IsUnit z.2.2.2.1.det}

/-- The raw determinant-chart set is open. -/
theorem isOpen_productReductionStepRawDetChartSet
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] :
    IsOpen (productReductionStepRawDetChartSet ρ π μ ν) := by
  change IsOpen
    {z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ |
      IsUnit z.1.det ∧ IsUnit z.2.2.2.1.det}
  exact
    isOpen_productReductionStepRawTopologyTuple_detChart
      (ρ := ρ) (π := π) (μ := μ) (ν := ν)

/-- The raw determinant-chart set is null-measurable for any Borel-space
measure. -/
theorem nullMeasurableSet_productReductionStepRawDetChartSet
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    [MeasurableSpace (ProductReductionStepRawTopologyTuple ρ π μ ν)]
    [BorelSpace (ProductReductionStepRawTopologyTuple ρ π μ ν)]
    (m : Measure (ProductReductionStepRawTopologyTuple ρ π μ ν)) :
    NullMeasurableSet (productReductionStepRawDetChartSet ρ π μ ν) m :=
  (isOpen_productReductionStepRawDetChartSet
    (ρ := ρ) (π := π) (μ := μ) (ν := ν)).measurableSet.nullMeasurableSet

/-- The raw-order p. 13 product-step coordinate map. The chart output is
reordered into raw-shaped order so that the derivative is an endomorphism. -/
def productReductionStepTopologyTupleToChartRawOrder
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    (z : ProductReductionStepRawTopologyTuple ρ π μ ν) :
    ProductReductionStepRawTopologyTuple ρ π μ ν :=
  productReductionStepChartTangentRawOrderEquiv
    (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ)
    (productReductionStepTopologyTupleToChart
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) z)

/-- The continuous-linear derivative family for the raw-order p. 13
product-step coordinate map. -/
def productReductionStepRawOrderJacobianCLM
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    (z : ProductReductionStepRawTopologyTuple ρ π μ ν) :
    ProductReductionStepRawTopologyTuple ρ π μ ν →L[ℝ]
      ProductReductionStepRawTopologyTuple ρ π μ ν :=
  LinearMap.toContinuousLinearMap
    (productReductionStepFormalJacobianRawOrder
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ)
      (productReductionStepRawCoordinatesOfTopologyTuple z))

/-- The absolute determinant density of the raw-order product-step derivative. -/
def productReductionStepRawOrderJacobianAbsDet
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    (z : ProductReductionStepRawTopologyTuple ρ π μ ν) : ℝ :=
  |(productReductionStepRawOrderJacobianCLM
    (ρ := ρ) (π := π) (μ := μ) (ν := ν) z).det|

set_option maxRecDepth 2048 in
/-- On the raw determinant chart, the raw-order product-step map pushes the
weighted source Haar measure with density `|det DΦ|` to the Haar measure
restricted to the image. -/
theorem map_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart_withDensity_abs_det
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    [MeasurableSpace (ProductReductionStepRawTopologyTuple ρ π μ ν)]
    [BorelSpace (ProductReductionStepRawTopologyTuple ρ π μ ν)]
    (m : Measure (ProductReductionStepRawTopologyTuple ρ π μ ν))
    [m.IsAddHaarMeasure]
    (hs : NullMeasurableSet (productReductionStepRawDetChartSet ρ π μ ν) m) :
    Measure.map
        (productReductionStepTopologyTupleToChartRawOrder
          (ρ := ρ) (π := π) (μ := μ) (ν := ν))
        ((m.restrict (productReductionStepRawDetChartSet ρ π μ ν)).withDensity
          (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν =>
            ENNReal.ofReal
              (productReductionStepRawOrderJacobianAbsDet
                (ρ := ρ) (π := π) (μ := μ) (ν := ν) z))) =
      m.restrict
        (productReductionStepTopologyTupleToChartRawOrder
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) ''
            productReductionStepRawDetChartSet ρ π μ ν) := by
  have hf' :
      ∀ z ∈ productReductionStepRawDetChartSet ρ π μ ν,
        HasFDerivWithinAt
          (productReductionStepTopologyTupleToChartRawOrder
            (ρ := ρ) (π := π) (μ := μ) (ν := ν))
          (productReductionStepRawOrderJacobianCLM
            (ρ := ρ) (π := π) (μ := μ) (ν := ν) z)
          (productReductionStepRawDetChartSet ρ π μ ν) z := by
    intro z hz
    simpa [productReductionStepRawDetChartSet,
      productReductionStepTopologyTupleToChartRawOrder,
      productReductionStepRawOrderJacobianCLM,
      ProductReductionStepRawTopologyTuple] using
      (hasFDerivWithinAt_productReductionStepTopologyTupleToChart_rawOrder_detChart
        (ρ := ρ) (π := π) (μ := μ) (ν := ν)
        (productReductionStepRawCoordinatesOfTopologyTuple z) hz.1 hz.2)
  have hinj : Set.InjOn
      (productReductionStepTopologyTupleToChartRawOrder
        (ρ := ρ) (π := π) (μ := μ) (ν := ν))
      (productReductionStepRawDetChartSet ρ π μ ν) := by
    simpa [productReductionStepRawDetChartSet,
      productReductionStepTopologyTupleToChartRawOrder,
      ProductReductionStepRawTopologyTuple] using
      (injOn_productReductionStepTopologyTupleToChart_rawOrder_detChart
        (ρ := ρ) (π := π) (μ := μ) (ν := ν))
  simpa [productReductionStepRawOrderJacobianAbsDet] using
    MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
      (μ := m)
      (f' := productReductionStepRawOrderJacobianCLM
        (ρ := ρ) (π := π) (μ := μ) (ν := ν))
      hs hf' hinj

end Aoyagi
end DLN
end DLNFibre
