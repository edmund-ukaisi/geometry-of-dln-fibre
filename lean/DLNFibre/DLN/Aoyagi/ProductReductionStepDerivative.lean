import DLNFibre.DLN.Aoyagi.ProductReductionStepJacobian
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed

/-!
# Analytic derivative of Aoyagi's p. 13 product-step coordinate change

This file begins the analytic counterpart of the formal p. 13 tangent
calculation in `ProductReductionStepJacobian`.  The first checkpoint is the
matrix inverse derivative on determinant charts.  Later results should use it
to identify the ambient tuple derivative of the one-step coordinate change
with `productReductionStepFormalJacobian`.

These statements are local analytic coordinate facts.  They do not prove a
source-measure pushforward, density transport, normal crossings, pole order, or
RLCT extraction.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator
open scoped RightActions

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Heterogeneous finite matrix multiplication as a continuous bilinear map.

Mathlib gives the algebraic bilinear map as `Matrix.mulLinearMap`; finite
dimensionality upgrades each linear layer to a continuous linear map. -/
def matrixMulContinuousLinearMap
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] :
    Matrix l m ℝ →L[ℝ] Matrix m n ℝ →L[ℝ] Matrix l n ℝ :=
  let L : Matrix l m ℝ →ₗ[ℝ] Matrix m n ℝ →L[ℝ] Matrix l n ℝ :=
    (LinearMap.toContinuousLinearMap :
        (Matrix m n ℝ →ₗ[ℝ] Matrix l n ℝ) ≃ₗ[ℝ]
          Matrix m n ℝ →L[ℝ] Matrix l n ℝ).toLinearMap.comp
      (mulLinearMap ℝ)
  LinearMap.toContinuousLinearMap L

@[simp]
theorem matrixMulContinuousLinearMap_apply
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    matrixMulContinuousLinearMap (l := l) (m := m) (n := n) A B = A * B := by
  simp [matrixMulContinuousLinearMap]

/-- Matrix inversion is Frechet differentiable at determinant-unit real square
matrices, with derivative `H ↦ -A⁻¹ H A⁻¹`.

This is the analytic inverse-derivative input for the p. 13 product-step
coordinate formulas. -/
theorem hasFDerivAt_matrix_inv_of_isUnit_det
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (A : Matrix ρ ρ ℝ) (hA : IsUnit A.det) :
    HasFDerivAt (fun B : Matrix ρ ρ ℝ => B⁻¹)
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix ρ ρ ℝ) A⁻¹ A⁻¹)) A := by
  have hUnit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hA
  rcases hUnit with ⟨u, rfl⟩
  rw [show (fun B : Matrix ρ ρ ℝ => B⁻¹) = Ring.inverse from by
    funext B
    exact Matrix.nonsing_inv_eq_ringInverse (A := B)]
  rw [Matrix.nonsing_inv_eq_ringInverse (A := (u : Matrix ρ ρ ℝ))]
  rw [Ring.inverse_unit u]
  exact
    (hasFDerivAt_ringInverse (𝕜 := ℝ) (R := Matrix ρ ρ ℝ) u)

/-- Tuple-level version of `ProductReductionStepRawCoordinates.toChart`.

This is the ambient vector-space map used for Frechet derivative statements;
the record-level determinant-chart map is recovered by applying this to
`ProductReductionStepRawCoordinates.topologyTuple`. -/
def productReductionStepTopologyTupleToChart
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    (z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ) :
    ProductReductionStepChartCoordinates.TopologyTuple ρ π μ ν ℝ :=
  let C1 : Matrix ρ ρ ℝ := z.1
  let D : Matrix π μ ℝ := z.2.1
  let F3old : Matrix π ρ ℝ := z.2.2.1
  let A1 : Matrix ρ ρ ℝ := z.2.2.2.1
  let A2 : Matrix ρ ν ℝ := z.2.2.2.2.1
  let A3 : Matrix μ ρ ℝ := z.2.2.2.2.2.1
  let A4 : Matrix μ ν ℝ := z.2.2.2.2.2.2
  let Ctop : Matrix ρ ρ ℝ := C1 * A1
  (Ctop,
    (D,
      (A1,
        (A3,
          (-(A1⁻¹ * A2),
            (F3old - D * A3 * Ctop⁻¹,
              A4 - A3 * A1⁻¹ * A2))))))

@[simp]
theorem productReductionStepTopologyTupleToChart_topologyTuple
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [DecidableEq μ] [Fintype ν]
    (x : ProductReductionStepRawCoordinates ρ π μ ν ℝ) :
    productReductionStepTopologyTupleToChart
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) x.topologyTuple =
      ProductReductionStepChartCoordinates.topologyTuple x.toChart := by
  rfl

@[simp]
theorem productReductionStepTopologyTupleToChart_topologyTuple_chartBase
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    (x : ProductReductionStepRawCoordinates ρ π μ ν ℝ) :
    productReductionStepTopologyTupleToChart
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) x.topologyTuple =
      ProductReductionStepChartCoordinates.topologyTuple
        (productReductionStepFormalJacobianChartBase
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ) x) := by
  rfl

-- The matrix-ring product derivative theorem triggers deep right-action
-- typeclass search before reaching the componentwise simplification.
set_option maxRecDepth 2048 in
/-- The `Ctop = C1 * A1` component of the ambient tuple coordinate map has
the expected Frechet derivative from the formal p. 13 tangent calculation. -/
theorem hasFDerivAt_productReductionStepTopologyTupleToChart_Ctop
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Finite π]
    [Fintype μ] [Finite ν]
    (x : ProductReductionStepRawCoordinates ρ π μ ν ℝ) :
    HasFDerivAt
      (fun z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ =>
        (productReductionStepTopologyTupleToChart
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) z).1)
      (LinearMap.toContinuousLinearMap
        (productReductionStepFormalJacobian_dCtop
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ) x))
      x.topologyTuple := by
  let _ : Fintype π := Fintype.ofFinite π
  let _ : Fintype ν := Fintype.ofFinite ν
  let LC1 : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ →L[ℝ]
      Matrix ρ ρ ℝ :=
    LinearMap.toContinuousLinearMap
      (productReductionStepRawTangent_dC1
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ))
  let LA1 : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ →L[ℝ]
      Matrix ρ ρ ℝ :=
    LinearMap.toContinuousLinearMap
      (productReductionStepRawTangent_dA1
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ))
  have hC1 : HasFDerivAt
      (fun z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ => z.1)
      LC1 x.topologyTuple := by
    simpa [LC1, productReductionStepRawTangent_dC1] using
      (LC1.hasFDerivAt (x := x.topologyTuple))
  have hA1 : HasFDerivAt
      (fun z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ =>
        z.2.2.2.1)
      LA1 x.topologyTuple := by
    simpa [LA1, productReductionStepRawTangent_dA1] using
      (LA1.hasFDerivAt (x := x.topologyTuple))
  have hmul : HasFDerivAt
      (fun z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ =>
        z.1 * z.2.2.2.1)
      (x.C1 • LA1 + LC1 <• x.A1) x.topologyTuple :=
    hC1.mul' hA1
  have hderiv :
      LinearMap.toContinuousLinearMap
          (productReductionStepFormalJacobian_dCtop
            (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ) x) =
        x.C1 • LA1 + LC1 <• x.A1 := by
    apply ContinuousLinearMap.ext
    intro v
    ext i j
    simp [LC1, LA1, productReductionStepFormalJacobian_dCtop,
      productReductionStepRawTangent_dC1, productReductionStepRawTangent_dA1,
      Matrix.mul_apply]
    abel_nf
  rw [hderiv]
  simpa [productReductionStepTopologyTupleToChart] using hmul

-- The inverse and heterogeneous product derivatives both trigger deep
-- typeclass search before the final componentwise simplification.
set_option maxRecDepth 2048 in
/-- The `F2 = -A1⁻¹ * A2` component of the ambient tuple coordinate map has
the expected Frechet derivative from the formal p. 13 tangent calculation. -/
theorem hasFDerivAt_productReductionStepTopologyTupleToChart_F2
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Finite π]
    [Fintype μ] [Finite ν]
    (x : ProductReductionStepRawCoordinates ρ π μ ν ℝ)
    (hA1 : IsUnit x.A1.det) :
    HasFDerivAt
      (fun z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ =>
        (productReductionStepTopologyTupleToChart
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) z).2.2.2.2.1)
      (LinearMap.toContinuousLinearMap
        (productReductionStepFormalJacobian_dF2
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ) x))
      x.topologyTuple := by
  let _ : Fintype π := Fintype.ofFinite π
  let _ : Fintype ν := Fintype.ofFinite ν
  let LA1 : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ →L[ℝ]
      Matrix ρ ρ ℝ :=
    LinearMap.toContinuousLinearMap
      (productReductionStepRawTangent_dA1
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ))
  let LA2 : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ →L[ℝ]
      Matrix ρ ν ℝ :=
    LinearMap.toContinuousLinearMap
      (productReductionStepRawTangent_dA2
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ))
  let LinvA1 : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ →L[ℝ]
      Matrix ρ ρ ℝ :=
    (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix ρ ρ ℝ) x.A1⁻¹ x.A1⁻¹)).comp LA1
  let B : Matrix ρ ρ ℝ →L[ℝ] Matrix ρ ν ℝ →L[ℝ] Matrix ρ ν ℝ :=
    matrixMulContinuousLinearMap (l := ρ) (m := ρ) (n := ν)
  have hA1coord : HasFDerivAt
      (fun z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ =>
        z.2.2.2.1)
      LA1 x.topologyTuple := by
    simpa [LA1, productReductionStepRawTangent_dA1] using
      (LA1.hasFDerivAt (x := x.topologyTuple))
  have hA2coord : HasFDerivAt
      (fun z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ =>
        z.2.2.2.2.1)
      LA2 x.topologyTuple := by
    simpa [LA2, productReductionStepRawTangent_dA2] using
      (LA2.hasFDerivAt (x := x.topologyTuple))
  have hA1inv : HasFDerivAt
      (fun z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ =>
        (z.2.2.2.1)⁻¹)
      LinvA1 x.topologyTuple := by
    simpa [LinvA1, Function.comp_def] using
      ((hasFDerivAt_matrix_inv_of_isUnit_det x.A1 hA1).comp
        (x := x.topologyTuple) hA1coord)
  have hmul : HasFDerivAt
      (fun z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ =>
        (z.2.2.2.1)⁻¹ * z.2.2.2.2.1)
      (B.precompR _ x.A1⁻¹ LA2 + B.precompL _ LinvA1 x.A2)
      x.topologyTuple := by
    simpa [B] using
      (B.hasFDerivAt_of_bilinear hA1inv hA2coord)
  have hneg : HasFDerivAt
      (fun z : ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν ℝ =>
        -((z.2.2.2.1)⁻¹ * z.2.2.2.2.1))
      (-(B.precompR _ x.A1⁻¹ LA2 + B.precompL _ LinvA1 x.A2))
      x.topologyTuple :=
    hmul.neg
  have hderiv :
      LinearMap.toContinuousLinearMap
          (productReductionStepFormalJacobian_dF2
            (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := ℝ) x) =
        -(B.precompR _ x.A1⁻¹ LA2 + B.precompL _ LinvA1 x.A2) := by
    apply ContinuousLinearMap.ext
    intro v
    ext i j
    simp [B, LA1, LA2, LinvA1, productReductionStepFormalJacobian_dF2,
      productReductionStepRawTangent_dA1, productReductionStepRawTangent_dA2,
      Matrix.mul_apply]
    abel_nf
  rw [hderiv]
  simpa [productReductionStepTopologyTupleToChart] using hneg

end Aoyagi
end DLN
end DLNFibre
