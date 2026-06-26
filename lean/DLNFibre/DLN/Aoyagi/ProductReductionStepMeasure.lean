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
open scoped ENNReal Matrix.Norms.Operator Topology

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

@[simp]
theorem ProductReductionStepRawCoordinates.topologyTuple_mem_rawDetChartSet
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    (x : ProductReductionStepRawCoordinates ρ π μ ν ℝ) :
    x.topologyTuple ∈ productReductionStepRawDetChartSet ρ π μ ν ↔ x.detChart := by
  rfl

@[simp]
theorem productReductionStepRawCoordinatesOfTopologyTuple_of_topologyTuple
    {ρ π μ ν K : Type*}
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    productReductionStepRawCoordinatesOfTopologyTuple x.topologyTuple = x := by
  cases x
  rfl

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

/-- Interpret a raw-shaped target tuple `(Ctop,D,F3,A1,F2,A3,C)` as a chart
coordinate record. -/
def productReductionStepChartCoordinatesOfRawOrderTopologyTuple
    {ρ π μ ν : Type*}
    (z : ProductReductionStepRawTopologyTuple ρ π μ ν) :
    ProductReductionStepChartCoordinates ρ π μ ν ℝ where
  Ctop := z.1
  D := z.2.1
  A1 := z.2.2.2.1
  A3 := z.2.2.2.2.2.1
  F2 := z.2.2.2.2.1
  F3 := z.2.2.1
  C := z.2.2.2.2.2.2

@[simp]
theorem productReductionStepChartCoordinatesOfRawOrderTopologyTuple_detChart
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    (z : ProductReductionStepRawTopologyTuple ρ π μ ν) :
    (productReductionStepChartCoordinatesOfRawOrderTopologyTuple z).detChart ↔
      z ∈ productReductionStepRawDetChartSet ρ π μ ν := by
  rfl

@[simp]
theorem productReductionStepChartCoordinatesOfRawOrderTopologyTuple_rawOrder
    {ρ π μ ν : Type*}
    (z : ProductReductionStepRawTopologyTuple ρ π μ ν) :
    productReductionStepChartTangentRawOrderEquiv
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ)
        ((productReductionStepChartCoordinatesOfRawOrderTopologyTuple z).topologyTuple) = z := by
  rfl

@[simp]
theorem ProductReductionStepChartCoordinates.rawOrderTopologyTuple_mem_rawDetChartSet
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    (y : ProductReductionStepChartCoordinates ρ π μ ν ℝ) :
    productReductionStepChartTangentRawOrderEquiv
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ) y.topologyTuple ∈
      productReductionStepRawDetChartSet ρ π μ ν ↔ y.detChart := by
  rfl

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

/-- The determinant of the raw-order product-step derivative family is a unit
on the determinant chart. -/
theorem productReductionStepRawOrderJacobianCLM_det_isUnit
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    (z : ProductReductionStepRawTopologyTuple ρ π μ ν)
    (hz : z ∈ productReductionStepRawDetChartSet ρ π μ ν) :
    IsUnit
      ((productReductionStepRawOrderJacobianCLM
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) z).det) := by
  let x : ProductReductionStepRawCoordinates ρ π μ ν ℝ :=
    productReductionStepRawCoordinatesOfTopologyTuple z
  have hx : x.detChart := by
    simpa [x, productReductionStepRawDetChartSet] using hz
  simpa [productReductionStepRawOrderJacobianCLM, x] using
    (productReductionStepFormalJacobianRawOrder_det_isUnit
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ) x hx.1 hx.2)

/-- The absolute determinant density of the raw-order product-step derivative
is positive on the determinant chart. -/
theorem productReductionStepRawOrderJacobianAbsDet_pos
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    (z : ProductReductionStepRawTopologyTuple ρ π μ ν)
    (hz : z ∈ productReductionStepRawDetChartSet ρ π μ ν) :
    0 < productReductionStepRawOrderJacobianAbsDet
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) z := by
  have hunit :=
    productReductionStepRawOrderJacobianCLM_det_isUnit
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) z hz
  rw [productReductionStepRawOrderJacobianAbsDet]
  exact abs_pos.mpr (isUnit_iff_ne_zero.mp hunit)

/-- Near any determinant-chart point, the absolute determinant density of the
raw-order product-step derivative is positive. -/
theorem eventually_productReductionStepRawOrderJacobianAbsDet_pos_nhds
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    (z₀ : ProductReductionStepRawTopologyTuple ρ π μ ν)
    (hz₀ : z₀ ∈ productReductionStepRawDetChartSet ρ π μ ν) :
    ∀ᶠ z in 𝓝 z₀,
      0 < productReductionStepRawOrderJacobianAbsDet
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) z := by
  filter_upwards [
    (isOpen_productReductionStepRawDetChartSet
      (ρ := ρ) (π := π) (μ := μ) (ν := ν)).mem_nhds hz₀] with z hz
  exact
    productReductionStepRawOrderJacobianAbsDet_pos
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) z hz

/-- Applying the raw-order product-step derivative family to a fixed tangent
vector varies continuously at determinant-chart points. -/
theorem continuousAt_productReductionStepRawOrderJacobianCLM_apply_of_mem_rawDetChartSet
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    (z₀ : ProductReductionStepRawTopologyTuple ρ π μ ν)
    (hz₀ : z₀ ∈ productReductionStepRawDetChartSet ρ π μ ν)
    (v : ProductReductionStepRawTopologyTuple ρ π μ ν) :
    ContinuousAt
      (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν =>
        productReductionStepRawOrderJacobianCLM
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) z v)
      z₀ := by
  let dC1 : Matrix ρ ρ ℝ := v.1
  let dD : Matrix π μ ℝ := v.2.1
  let dF3old : Matrix π ρ ℝ := v.2.2.1
  let dA1 : Matrix ρ ρ ℝ := v.2.2.2.1
  let dA2 : Matrix ρ ν ℝ := v.2.2.2.2.1
  let dA3 : Matrix μ ρ ℝ := v.2.2.2.2.2.1
  let dA4 : Matrix μ ν ℝ := v.2.2.2.2.2.2
  have hA1 : ContinuousAt
      (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν => z.2.2.2.1) z₀ := by
    fun_prop
  have hA1inv : ContinuousAt
      (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν => (z.2.2.2.1)⁻¹) z₀ :=
    ContinuousAt.comp
      (x := z₀)
      (f := fun z : ProductReductionStepRawTopologyTuple ρ π μ ν => z.2.2.2.1)
      (g := fun A : Matrix ρ ρ ℝ => A⁻¹)
      (continuousAt_matrix_inv_of_isUnit_det (A := z₀.2.2.2.1) hz₀.2) hA1
  have hCtop : ContinuousAt
      (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν => z.1 * z.2.2.2.1) z₀ := by
    fun_prop
  have hCtopUnit : IsUnit (z₀.1 * z₀.2.2.2.1).det := by
    simpa [Matrix.det_mul] using hz₀.1.mul hz₀.2
  have hCtopInv : ContinuousAt
      (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν => (z.1 * z.2.2.2.1)⁻¹) z₀ :=
    ContinuousAt.comp
      (x := z₀)
      (f := fun z : ProductReductionStepRawTopologyTuple ρ π μ ν =>
        z.1 * z.2.2.2.1)
      (g := fun A : Matrix ρ ρ ℝ => A⁻¹)
      (continuousAt_matrix_inv_of_isUnit_det
        (A := z₀.1 * z₀.2.2.2.1) hCtopUnit) hCtop
  have hdCtop : ContinuousAt
      (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν =>
        dC1 * z.2.2.2.1 + z.1 * dA1) z₀ := by
    fun_prop
  have hdF2 : ContinuousAt
      (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν =>
        (z.2.2.2.1)⁻¹ * dA1 * (z.2.2.2.1)⁻¹ * z.2.2.2.2.1 -
          (z.2.2.2.1)⁻¹ * dA2) z₀ := by
    fun_prop
  have hdF3 : ContinuousAt
      (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν =>
        dF3old
          - dD * z.2.2.2.2.2.1 * (z.1 * z.2.2.2.1)⁻¹
          - z.2.1 * dA3 * (z.1 * z.2.2.2.1)⁻¹
          + z.2.1 * z.2.2.2.2.2.1 * (z.1 * z.2.2.2.1)⁻¹ *
              (dC1 * z.2.2.2.1 + z.1 * dA1) *
                (z.1 * z.2.2.2.1)⁻¹) z₀ := by
    fun_prop
  have hdC : ContinuousAt
      (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν =>
        dA4
          - dA3 * (z.2.2.2.1)⁻¹ * z.2.2.2.2.1
          + z.2.2.2.2.2.1 * (z.2.2.2.1)⁻¹ * dA1 *
              (z.2.2.2.1)⁻¹ * z.2.2.2.2.1
          - z.2.2.2.2.2.1 * (z.2.2.2.1)⁻¹ * dA2) z₀ := by
    fun_prop
  simpa [productReductionStepRawOrderJacobianCLM,
    productReductionStepFormalJacobianRawOrder,
    productReductionStepFormalJacobian_apply,
    productReductionStepFormalJacobianFormula,
    productReductionStepChartTangentRawOrderEquiv,
    productReductionStepRawCoordinatesOfTopologyTuple,
    dC1, dD, dF3old, dA1, dA2, dA3, dA4] using
      hdCtop.prodMk
        ((continuousAt_const : ContinuousAt
          (fun _ : ProductReductionStepRawTopologyTuple ρ π μ ν => dD) z₀).prodMk
          (hdF3.prodMk
            ((continuousAt_const : ContinuousAt
              (fun _ : ProductReductionStepRawTopologyTuple ρ π μ ν => dA1) z₀).prodMk
              (hdF2.prodMk
                ((continuousAt_const : ContinuousAt
                  (fun _ : ProductReductionStepRawTopologyTuple ρ π μ ν => dA3) z₀).prodMk
                  hdC)))))

/-- The raw-order product-step derivative family is continuous at
determinant-chart points. -/
theorem continuousAt_productReductionStepRawOrderJacobianCLM_of_mem_rawDetChartSet
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    (z₀ : ProductReductionStepRawTopologyTuple ρ π μ ν)
    (hz₀ : z₀ ∈ productReductionStepRawDetChartSet ρ π μ ν) :
    ContinuousAt
      (productReductionStepRawOrderJacobianCLM
        (ρ := ρ) (π := π) (μ := μ) (ν := ν))
      z₀ := by
  classical
  let E : Type _ := ProductReductionStepRawTopologyTuple ρ π μ ν
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let J : E → E →L[ℝ] E :=
    productReductionStepRawOrderJacobianCLM
      (ρ := ρ) (π := π) (μ := μ) (ν := ν)
  let M : E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun z => LinearMap.toMatrix b b ((J z : E →ₗ[ℝ] E))
  have hM : ContinuousAt M z₀ := by
    refine continuousAt_pi.2 ?_
    intro i
    refine continuousAt_pi.2 ?_
    intro j
    have happ : ContinuousAt (fun z : E => J z (b j)) z₀ := by
      simpa [E, J] using
        continuousAt_productReductionStepRawOrderJacobianCLM_apply_of_mem_rawDetChartSet
          (ρ := ρ) (π := π) (μ := μ) (ν := ν)
          (z₀ := z₀) (hz₀ := hz₀) (v := b j)
    have hcoord : ContinuousAt (fun z : E => b.coord i (J z (b j))) z₀ :=
      (b.coord i).continuous_of_finiteDimensional.continuousAt.comp happ
    simpa [M, LinearMap.toMatrix_apply] using hcoord
  have hrealize : ContinuousAt
      (fun A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ =>
        LinearMap.toContinuousLinearMap (Matrix.toLin b b A))
      (M z₀) :=
    (continuous_matrix_toContinuousLinearMap b b).continuousAt
  have hcomp : ContinuousAt
      (fun z : E =>
        LinearMap.toContinuousLinearMap (Matrix.toLin b b (M z)))
      z₀ :=
    hrealize.comp hM
  convert hcomp using 1
  funext z
  apply ContinuousLinearMap.ext
  intro v
  change J z v =
    Matrix.toLin b b
      (LinearMap.toMatrix b b ((J z : E →ₗ[ℝ] E))) v
  rw [Matrix.toLin_toMatrix]
  rfl

set_option maxRecDepth 2048 in
/-- The absolute determinant density of the raw-order product-step derivative
is continuous at determinant-chart points. -/
theorem continuousAt_productReductionStepRawOrderJacobianAbsDet_of_mem_rawDetChartSet
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    (z₀ : ProductReductionStepRawTopologyTuple ρ π μ ν)
    (hz₀ : z₀ ∈ productReductionStepRawDetChartSet ρ π μ ν) :
    ContinuousAt
      (productReductionStepRawOrderJacobianAbsDet
        (ρ := ρ) (π := π) (μ := μ) (ν := ν))
      z₀ := by
  have hJ :=
    continuousAt_productReductionStepRawOrderJacobianCLM_of_mem_rawDetChartSet
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) z₀ hz₀
  change ContinuousAt
    (fun z : ProductReductionStepRawTopologyTuple ρ π μ ν =>
      |(productReductionStepRawOrderJacobianCLM
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) z).det|)
    z₀
  exact (ContinuousLinearMap.continuous_det.continuousAt.comp hJ).abs

/-- Near any determinant-chart point, the raw-order product-step Jacobian
density admits a positive lower bound. -/
theorem exists_pos_eventually_le_productReductionStepRawOrderJacobianAbsDet_nhds
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    (z₀ : ProductReductionStepRawTopologyTuple ρ π μ ν)
    (hz₀ : z₀ ∈ productReductionStepRawDetChartSet ρ π μ ν) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ z in 𝓝 z₀,
        ε ≤ productReductionStepRawOrderJacobianAbsDet
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) z := by
  let density : ProductReductionStepRawTopologyTuple ρ π μ ν → ℝ :=
    productReductionStepRawOrderJacobianAbsDet
      (ρ := ρ) (π := π) (μ := μ) (ν := ν)
  have hdensity : ContinuousAt density z₀ :=
    continuousAt_productReductionStepRawOrderJacobianAbsDet_of_mem_rawDetChartSet
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) z₀ hz₀
  have hpos : 0 < density z₀ :=
    productReductionStepRawOrderJacobianAbsDet_pos
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) z₀ hz₀
  refine ⟨density z₀ / 2, half_pos hpos, ?_⟩
  have htarget : ∀ᶠ y in 𝓝 (density z₀), density z₀ / 2 ≤ y := by
    exact eventually_ge_nhds (show density z₀ / 2 < density z₀ by linarith)
  exact hdensity.eventually htarget

/-- Near any determinant-chart point, the raw-order product-step Jacobian
density admits a positive upper bound. -/
theorem exists_pos_eventually_productReductionStepRawOrderJacobianAbsDet_le_nhds
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [Fintype μ] [Fintype ν]
    (z₀ : ProductReductionStepRawTopologyTuple ρ π μ ν)
    (hz₀ : z₀ ∈ productReductionStepRawDetChartSet ρ π μ ν) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ z in 𝓝 z₀,
        productReductionStepRawOrderJacobianAbsDet
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) z ≤ K := by
  let density : ProductReductionStepRawTopologyTuple ρ π μ ν → ℝ :=
    productReductionStepRawOrderJacobianAbsDet
      (ρ := ρ) (π := π) (μ := μ) (ν := ν)
  have hdensity : ContinuousAt density z₀ :=
    continuousAt_productReductionStepRawOrderJacobianAbsDet_of_mem_rawDetChartSet
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) z₀ hz₀
  refine ⟨max (density z₀ + 1) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · have htarget : ∀ᶠ y in 𝓝 (density z₀), y ≤ density z₀ + 1 := by
      exact eventually_le_nhds (show density z₀ < density z₀ + 1 by linarith)
    exact (hdensity.eventually htarget).mono
      (fun _ hz ↦ hz.trans (le_max_left _ _))

/-- The raw-order p. 13 product-step map preserves the determinant chart. -/
theorem mapsTo_productReductionStepTopologyTupleToChartRawOrder_detChart
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    [Fintype μ] [Finite ν] :
    Set.MapsTo
      (productReductionStepTopologyTupleToChartRawOrder
        (ρ := ρ) (π := π) (μ := μ) (ν := ν))
      (productReductionStepRawDetChartSet ρ π μ ν)
      (productReductionStepRawDetChartSet ρ π μ ν) := by
  classical
  let _ : Fintype ν := Fintype.ofFinite ν
  intro z hz
  let x : ProductReductionStepRawCoordinates ρ π μ ν ℝ :=
    productReductionStepRawCoordinatesOfTopologyTuple z
  have hx : x.detChart := by
    simpa [x, productReductionStepRawDetChartSet] using hz
  have hchart : x.toChart.detChart :=
    ProductReductionStepRawCoordinates.detChart_toChart x hx
  have hraw :
      productReductionStepChartTangentRawOrderEquiv
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ) x.toChart.topologyTuple ∈
        productReductionStepRawDetChartSet ρ π μ ν := by
    simpa using
      (ProductReductionStepChartCoordinates.rawOrderTopologyTuple_mem_rawDetChartSet
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) x.toChart).2 hchart
  simpa [productReductionStepTopologyTupleToChartRawOrder, x] using hraw

/-- The raw-order p. 13 product-step map is onto the raw-shaped determinant
chart. -/
theorem surjOn_productReductionStepTopologyTupleToChartRawOrder_detChart
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    [Fintype μ] [Finite ν] :
    Set.SurjOn
      (productReductionStepTopologyTupleToChartRawOrder
        (ρ := ρ) (π := π) (μ := μ) (ν := ν))
      (productReductionStepRawDetChartSet ρ π μ ν)
      (productReductionStepRawDetChartSet ρ π μ ν) := by
  classical
  let _ : Fintype ν := Fintype.ofFinite ν
  intro z hz
  let y : ProductReductionStepChartCoordinates ρ π μ ν ℝ :=
    productReductionStepChartCoordinatesOfRawOrderTopologyTuple z
  have hy : y.detChart := by
    simpa [y]
  refine ⟨(y.toRaw).topologyTuple, ?_, ?_⟩
  · simpa using
      (ProductReductionStepChartCoordinates.detChart_toRaw y hy)
  · have hright : (ProductReductionStepChartCoordinates.toRaw y).toChart = y :=
      productReductionStepCoordinate_right_inverse y hy.2 hy.1
    calc
      productReductionStepTopologyTupleToChartRawOrder
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (y.toRaw).topologyTuple =
        productReductionStepChartTangentRawOrderEquiv
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ)
          (ProductReductionStepChartCoordinates.topologyTuple
            ((ProductReductionStepChartCoordinates.toRaw y).toChart)) := by
          simp [productReductionStepTopologyTupleToChartRawOrder]
      _ =
        productReductionStepChartTangentRawOrderEquiv
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ)
          (ProductReductionStepChartCoordinates.topologyTuple y) := by
          rw [hright]
      _ = z := by
          simp [y]

/-- The raw-order p. 13 product-step map is a bijection on the raw-shaped
determinant chart. -/
theorem bijOn_productReductionStepTopologyTupleToChartRawOrder_detChart
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Finite π]
    [Fintype μ] [Finite ν] :
    Set.BijOn
      (productReductionStepTopologyTupleToChartRawOrder
        (ρ := ρ) (π := π) (μ := μ) (ν := ν))
      (productReductionStepRawDetChartSet ρ π μ ν)
      (productReductionStepRawDetChartSet ρ π μ ν) := by
  refine ⟨
    mapsTo_productReductionStepTopologyTupleToChartRawOrder_detChart
      (ρ := ρ) (π := π) (μ := μ) (ν := ν),
    ?_,
    surjOn_productReductionStepTopologyTupleToChartRawOrder_detChart
      (ρ := ρ) (π := π) (μ := μ) (ν := ν)⟩
  simpa [productReductionStepTopologyTupleToChartRawOrder,
    productReductionStepRawDetChartSet] using
    (injOn_productReductionStepTopologyTupleToChart_rawOrder_detChart
      (ρ := ρ) (π := π) (μ := μ) (ν := ν))

/-- The image of the raw determinant chart under the raw-order p. 13
product-step map is the raw-shaped determinant chart. -/
theorem image_productReductionStepTopologyTupleToChartRawOrder_detChart
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Finite π]
    [Fintype μ] [Finite ν] :
    productReductionStepTopologyTupleToChartRawOrder
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) ''
      productReductionStepRawDetChartSet ρ π μ ν =
        productReductionStepRawDetChartSet ρ π μ ν := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact
      mapsTo_productReductionStepTopologyTupleToChartRawOrder_detChart
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) hx
  · intro hz
    exact
      surjOn_productReductionStepTopologyTupleToChartRawOrder_detChart
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) hz

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

set_option maxRecDepth 2048 in
/-- On the raw determinant chart, the raw-order product-step map pushes the
weighted source Haar measure with density `|det DΦ|` to the Haar measure
restricted to the raw-shaped target determinant chart. -/
theorem map_productReductionStepRawOrder_restrict_detChart_withDensity_absDet_eq_restrict_detChart
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
      m.restrict (productReductionStepRawDetChartSet ρ π μ ν) := by
  simpa [image_productReductionStepTopologyTupleToChartRawOrder_detChart
      (ρ := ρ) (π := π) (μ := μ) (ν := ν)] using
    map_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart_withDensity_abs_det
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) m hs

end Aoyagi
end DLN
end DLNFibre
