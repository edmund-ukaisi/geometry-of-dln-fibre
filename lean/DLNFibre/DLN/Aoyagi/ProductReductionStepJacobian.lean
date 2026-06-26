import DLNFibre.DLN.Aoyagi.ChartTopology
import Mathlib.Data.Matrix.Bilinear
import Mathlib.LinearAlgebra.Determinant

/-!
# Formal Jacobian unit for Aoyagi's Schur coordinate core

This file records the finite linear calculation behind the Schur coordinate
replacement in Aoyagi's Lemma 2:

`F2 = -B⁻¹ A2`, `F3 = -A3 B⁻¹`, and
`C4 = A4 - A3 B⁻¹ A2`.

The result is formal tangent/Jacobian arithmetic only.  It does not prove an
analytic derivative theorem, a source-measure pushforward, density transport,
normal crossings, pole order, or RLCT extraction.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

variable {ρ μ ν K : Type*} [CommRing K]
variable [Fintype ρ] [DecidableEq ρ]

/-- Common tangent space for the Schur core variables.  The raw variables
`(A2,A3,A4)` and chart variables `(F2,F3,C4)` have the same matrix shapes. -/
abbrev SchurCoreTangent :=
  Matrix ρ ν K × (Matrix μ ρ K × Matrix μ ν K)

/-- Formal differential of Aoyagi's Schur coordinate core at fixed
`B, A2, A3`.

The coordinate formula is
`F2 = -B⁻¹ A2`, `F3 = -A3 B⁻¹`, and
`C4 = A4 - A3 B⁻¹ A2`.  This definition is the finite linearized map on
increments `(dA2,dA3,dA4)`. -/
def schurCoreFormalJacobian
    (B : Matrix ρ ρ K) (A2 : Matrix ρ ν K) (A3 : Matrix μ ρ K) :
    SchurCoreTangent (ρ := ρ) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      SchurCoreTangent (ρ := ρ) (μ := μ) (ν := ν) (K := K) where
  toFun v :=
    let dA2 : Matrix ρ ν K := v.1
    let dA3 : Matrix μ ρ K := v.2.1
    let dA4 : Matrix μ ν K := v.2.2
    let dF2 : Matrix ρ ν K := -(B⁻¹ * dA2)
    let dF3 : Matrix μ ρ K := -(dA3 * B⁻¹)
    let dC4 : Matrix μ ν K := dA4 - dA3 * B⁻¹ * A2 - A3 * B⁻¹ * dA2
    (dF2, (dF3, dC4))
  map_add' v w := by
    rcases v with ⟨dA2, dA3, dA4⟩
    rcases w with ⟨eA2, eA3, eA4⟩
    apply Prod.ext
    · ext i j
      simp [Matrix.mul_add]
      ac_rfl
    · apply Prod.ext
      · ext i j
        simp [Matrix.add_mul]
        ac_rfl
      · ext i j
        simp [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm]
  map_smul' a v := by
    rcases v with ⟨dA2, dA3, dA4⟩
    apply Prod.ext
    · ext i j
      simp [Matrix.mul_smul]
    · apply Prod.ext
      · ext i j
        simp [Matrix.smul_mul]
      · ext i j
        simp [Matrix.smul_mul, Matrix.mul_smul, sub_eq_add_neg]

/-- Formal inverse differential for `schurCoreFormalJacobian`.

It is the linearization of
`A2 = -B F2`, `A3 = -F3 B`, and `A4 = C4 + F3 B F2`, rewritten at the base
point using `F2 = -B⁻¹ A2` and `F3 = -A3 B⁻¹`. -/
def schurCoreFormalJacobianInverse
    (B : Matrix ρ ρ K) (A2 : Matrix ρ ν K) (A3 : Matrix μ ρ K) :
    SchurCoreTangent (ρ := ρ) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      SchurCoreTangent (ρ := ρ) (μ := μ) (ν := ν) (K := K) where
  toFun v :=
    let eF2 : Matrix ρ ν K := v.1
    let eF3 : Matrix μ ρ K := v.2.1
    let eC4 : Matrix μ ν K := v.2.2
    let eA2 : Matrix ρ ν K := -B * eF2
    let eA3 : Matrix μ ρ K := -eF3 * B
    let eA4 : Matrix μ ν K := eC4 - eF3 * A2 - A3 * eF2
    (eA2, (eA3, eA4))
  map_add' v w := by
    rcases v with ⟨eF2, eF3, eC4⟩
    rcases w with ⟨fF2, fF3, fC4⟩
    apply Prod.ext
    · ext i j
      simp [Matrix.mul_add]
    · apply Prod.ext
      · ext i j
        simp [Matrix.add_mul]
        ac_rfl
      · ext i j
        simp [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm]
  map_smul' a v := by
    rcases v with ⟨eF2, eF3, eC4⟩
    apply Prod.ext
    · ext i j
      simp [Matrix.mul_smul]
    · apply Prod.ext
      · ext i j
        simp [Matrix.smul_mul]
      · ext i j
        simp [Matrix.smul_mul, Matrix.mul_smul, sub_eq_add_neg]

/-- Aoyagi's Schur coordinate core has an invertible formal differential on
the determinant chart `det B` a unit. -/
def schurCoreFormalJacobianEquiv
    (B : Matrix ρ ρ K) (A2 : Matrix ρ ν K) (A3 : Matrix μ ρ K)
    (hB : IsUnit B.det) :
    SchurCoreTangent (ρ := ρ) (μ := μ) (ν := ν) (K := K) ≃ₗ[K]
      SchurCoreTangent (ρ := ρ) (μ := μ) (ν := ν) (K := K) :=
  LinearEquiv.ofLinear
    (schurCoreFormalJacobian
      (ρ := ρ) (μ := μ) (ν := ν) (K := K) B A2 A3)
    (schurCoreFormalJacobianInverse
      (ρ := ρ) (μ := μ) (ν := ν) (K := K) B A2 A3)
    (by
      ext v <;>
        simp [schurCoreFormalJacobian, schurCoreFormalJacobianInverse, hB,
          Matrix.mul_nonsing_inv_cancel_left, Matrix.nonsing_inv_mul_cancel_left,
          Matrix.mul_assoc, sub_eq_add_neg, add_left_comm, add_comm])
    (by
      ext v <;>
        simp [schurCoreFormalJacobian, schurCoreFormalJacobianInverse, hB,
          Matrix.mul_nonsing_inv_cancel_left, Matrix.mul_assoc, sub_eq_add_neg,
          add_left_comm, add_comm])

/-- The formal Schur-core Jacobian determinant is a unit on the determinant
chart.

This is the nonvanishing finite determinant calculation used by the triangular
coordinate change.  It is not a source-measure or analytic pushforward theorem. -/
theorem schurCoreFormalJacobian_det_isUnit
    [Finite μ] [Finite ν]
    (B : Matrix ρ ρ K) (A2 : Matrix ρ ν K) (A3 : Matrix μ ρ K)
    (hB : IsUnit B.det) :
    IsUnit
      (LinearMap.det
        (schurCoreFormalJacobian
          (ρ := ρ) (μ := μ) (ν := ν) (K := K) B A2 A3)) := by
  let _ : Fintype μ := Fintype.ofFinite μ
  let _ : Fintype ν := Fintype.ofFinite ν
  exact LinearEquiv.isUnit_det'
    (schurCoreFormalJacobianEquiv
      (ρ := ρ) (μ := μ) (ν := ν) (K := K) B A2 A3 hB)

section ProductStepFixedPassive

variable {π : Type*} [Fintype μ]

/-- Tangent space for the fixed-passive product-step variables
`(C1,F3old,A2,A4)`.

Here `A1`, `D`, and `A3` are fixed parameters.  This is the p. 13 one-step
coordinate change beyond the Schur core, but not yet the full tangent map for
all raw fields. -/
abbrev ProductStepFixedPassiveRawTangent :=
  Matrix ρ ρ K × (Matrix π ρ K × (Matrix ρ ν K × Matrix μ ν K))

/-- Tangent space for the fixed-passive chart variables `(Ctop,F3,F2,C)`. -/
abbrev ProductStepFixedPassiveChartTangent :=
  Matrix ρ ρ K × (Matrix π ρ K × (Matrix ρ ν K × Matrix μ ν K))

/-- Formal differential of the fixed-passive p. 13 one-step product-reduction
coordinate change.

The fixed parameters are `D`, `A1`, and `A3`; the raw variables are
`(C1,F3old,A2,A4)`, and the chart variables are `(Ctop,F3,F2,C)`. -/
def productStepFixedPassiveFormalJacobian
    (C1 : Matrix ρ ρ K) (D : Matrix π μ K)
    (A1 : Matrix ρ ρ K) (A3 : Matrix μ ρ K) :
    ProductStepFixedPassiveRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      ProductStepFixedPassiveChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) where
  toFun v :=
    let dC1 : Matrix ρ ρ K := v.1
    let dF3old : Matrix π ρ K := v.2.1
    let dA2 : Matrix ρ ν K := v.2.2.1
    let dA4 : Matrix μ ν K := v.2.2.2
    let Ctop : Matrix ρ ρ K := C1 * A1
    let dCtop : Matrix ρ ρ K := dC1 * A1
    let dF2 : Matrix ρ ν K := -(A1⁻¹ * dA2)
    let dF3 : Matrix π ρ K :=
      dF3old + D * A3 * Ctop⁻¹ * dCtop * Ctop⁻¹
    let dC : Matrix μ ν K := dA4 - A3 * A1⁻¹ * dA2
    (dCtop, (dF3, (dF2, dC)))
  map_add' v w := by
    rcases v with ⟨dC1, dF3old, dA2, dA4⟩
    rcases w with ⟨eC1, eF3old, eA2, eA4⟩
    apply Prod.ext
    · ext i j
      simp [Matrix.add_mul]
    · apply Prod.ext
      · ext i j
        simp [Matrix.add_mul, Matrix.mul_add]
        abel_nf
      · apply Prod.ext
        · ext i j
          simp [Matrix.mul_add]
          ac_rfl
        · ext i j
          simp [Matrix.mul_add, sub_eq_add_neg]
          abel_nf
  map_smul' a v := by
    rcases v with ⟨dC1, dF3old, dA2, dA4⟩
    apply Prod.ext
    · ext i j
      simp
    · apply Prod.ext
      · ext i j
        simp [Matrix.smul_mul, Matrix.mul_smul, smul_add]
      · apply Prod.ext
        · ext i j
          simp [Matrix.mul_smul]
        · ext i j
          simp [Matrix.mul_smul, sub_eq_add_neg]

/-- Formal differential of the inverse fixed-passive p. 13 coordinate change. -/
def productStepFixedPassiveFormalJacobianInverse
    (D : Matrix π μ K) (A1 : Matrix ρ ρ K) (A3 : Matrix μ ρ K)
    (Ctop : Matrix ρ ρ K) :
    ProductStepFixedPassiveChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      ProductStepFixedPassiveRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) where
  toFun v :=
    let dCtop : Matrix ρ ρ K := v.1
    let dF3 : Matrix π ρ K := v.2.1
    let dF2 : Matrix ρ ν K := v.2.2.1
    let dC : Matrix μ ν K := v.2.2.2
    let dC1 : Matrix ρ ρ K := dCtop * A1⁻¹
    let dF3old : Matrix π ρ K :=
      dF3 - D * A3 * Ctop⁻¹ * dCtop * Ctop⁻¹
    let dA2 : Matrix ρ ν K := -A1 * dF2
    let dA4 : Matrix μ ν K := dC - A3 * dF2
    (dC1, (dF3old, (dA2, dA4)))
  map_add' v w := by
    rcases v with ⟨dCtop, dF3, dF2, dC⟩
    rcases w with ⟨eCtop, eF3, eF2, eC⟩
    apply Prod.ext
    · ext i j
      simp [Matrix.add_mul]
    · apply Prod.ext
      · ext i j
        simp [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg]
        abel_nf
      · apply Prod.ext
        · ext i j
          simp [Matrix.mul_add]
        · ext i j
          simp [Matrix.mul_add, sub_eq_add_neg]
          abel_nf
  map_smul' a v := by
    rcases v with ⟨dCtop, dF3, dF2, dC⟩
    apply Prod.ext
    · ext i j
      simp
    · apply Prod.ext
      · ext i j
        simp [Matrix.smul_mul, Matrix.mul_smul, sub_eq_add_neg]
      · apply Prod.ext
        · ext i j
          simp [Matrix.mul_smul]
        · ext i j
          simp [Matrix.mul_smul, sub_eq_add_neg]

/-- The fixed-passive p. 13 coordinate change has an invertible formal
differential on the determinant chart. -/
def productStepFixedPassiveFormalJacobianEquiv
    (C1 : Matrix ρ ρ K) (D : Matrix π μ K)
    (A1 : Matrix ρ ρ K) (A3 : Matrix μ ρ K)
    (hC1 : IsUnit C1.det) (hA1 : IsUnit A1.det) :
    ProductStepFixedPassiveRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) ≃ₗ[K]
      ProductStepFixedPassiveChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) :=
by
  have _hCtop : IsUnit (C1 * A1).det := by
    simpa [Matrix.det_mul] using hC1.mul hA1
  exact
  LinearEquiv.ofLinear
    (productStepFixedPassiveFormalJacobian
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) C1 D A1 A3)
    (productStepFixedPassiveFormalJacobianInverse
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) D A1 A3 (C1 * A1))
    (by
      apply LinearMap.ext
      intro v
      rcases v with ⟨dCtop, dF3, dF2, dC⟩
      apply Prod.ext
      · ext i j
        simp [productStepFixedPassiveFormalJacobian,
          productStepFixedPassiveFormalJacobianInverse, hA1, Matrix.mul_assoc]
      · apply Prod.ext
        · ext i j
          simp [productStepFixedPassiveFormalJacobian,
            productStepFixedPassiveFormalJacobianInverse, hA1, Matrix.mul_assoc,
            sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        · apply Prod.ext
          · ext i j
            simp [productStepFixedPassiveFormalJacobian,
              productStepFixedPassiveFormalJacobianInverse,
              Matrix.nonsing_inv_mul_cancel_left, hA1, Matrix.mul_assoc]
          · ext i j
            simp [productStepFixedPassiveFormalJacobian,
              productStepFixedPassiveFormalJacobianInverse,
              Matrix.nonsing_inv_mul_cancel_left, hA1, Matrix.mul_assoc,
              sub_eq_add_neg, add_assoc, add_left_comm, add_comm])
    (by
      apply LinearMap.ext
      intro v
      rcases v with ⟨dC1, dF3old, dA2, dA4⟩
      apply Prod.ext
      · ext i j
        simp [productStepFixedPassiveFormalJacobian,
          productStepFixedPassiveFormalJacobianInverse, hA1, Matrix.mul_assoc]
      · apply Prod.ext
        · ext i j
          simp [productStepFixedPassiveFormalJacobian,
            productStepFixedPassiveFormalJacobianInverse, hA1, Matrix.mul_assoc,
            sub_eq_add_neg, add_assoc]
        · apply Prod.ext
          · ext i j
            simp [productStepFixedPassiveFormalJacobian,
              productStepFixedPassiveFormalJacobianInverse,
              Matrix.mul_nonsing_inv_cancel_left, hA1, Matrix.mul_assoc]
          · ext i j
            simp [productStepFixedPassiveFormalJacobian,
              productStepFixedPassiveFormalJacobianInverse,
              Matrix.mul_nonsing_inv_cancel_left, hA1, Matrix.mul_assoc,
              sub_eq_add_neg, add_assoc])

/-- The fixed-passive p. 13 one-step formal Jacobian determinant is a unit on
the determinant chart.

This is a finite formal determinant statement, not a source-measure or density
transport theorem. -/
theorem productStepFixedPassiveFormalJacobian_det_isUnit
    [Finite π] [Finite ν]
    (C1 : Matrix ρ ρ K) (D : Matrix π μ K)
    (A1 : Matrix ρ ρ K) (A3 : Matrix μ ρ K)
    (hC1 : IsUnit C1.det) (hA1 : IsUnit A1.det) :
    IsUnit
      (LinearMap.det
        (productStepFixedPassiveFormalJacobian
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) C1 D A1 A3)) := by
  let _ : Fintype π := Fintype.ofFinite π
  let _ : Fintype ν := Fintype.ofFinite ν
  exact LinearEquiv.isUnit_det'
    (productStepFixedPassiveFormalJacobianEquiv
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) C1 D A1 A3 hC1 hA1)

end ProductStepFixedPassive

section ProductStepFull

variable {π : Type*} [Fintype μ]

/-- Tangent space for all raw variables in the p. 13 one-step product-reduction
coordinate change, ordered as `(C1,D,F3old,A1,A2,A3,A4)`. -/
abbrev ProductReductionStepRawTangent :=
  ProductReductionStepRawCoordinates.TopologyTuple ρ π μ ν K

/-- Tangent space for all chart variables in the p. 13 one-step
product-reduction coordinate change, ordered as `(Ctop,D,A1,A3,F2,F3,C)`. -/
abbrev ProductReductionStepChartTangent :=
  ProductReductionStepChartCoordinates.TopologyTuple ρ π μ ν K

/-- Full formal tangent formula for the p. 13 one-step product-reduction
coordinate change.

This is formal tangent arithmetic for the coordinate formulas in
`ProductReductionStepRawCoordinates.toChart`; it is not an analytic derivative
theorem or a source-measure pushforward statement. -/
def productReductionStepFormalJacobianFormula
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (v : ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)) :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) :=
  let dC1 : Matrix ρ ρ K := v.1
  let dD : Matrix π μ K := v.2.1
  let dF3old : Matrix π ρ K := v.2.2.1
  let dA1 : Matrix ρ ρ K := v.2.2.2.1
  let dA2 : Matrix ρ ν K := v.2.2.2.2.1
  let dA3 : Matrix μ ρ K := v.2.2.2.2.2.1
  let dA4 : Matrix μ ν K := v.2.2.2.2.2.2
  let Ctop : Matrix ρ ρ K := x.C1 * x.A1
  let dCtop : Matrix ρ ρ K := dC1 * x.A1 + x.C1 * dA1
  let dF2 : Matrix ρ ν K :=
    x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2 - x.A1⁻¹ * dA2
  let dF3 : Matrix π ρ K :=
    dF3old
      - dD * x.A3 * Ctop⁻¹
      - x.D * dA3 * Ctop⁻¹
      + x.D * x.A3 * Ctop⁻¹ * dCtop * Ctop⁻¹
  let dC : Matrix μ ν K :=
    dA4
      - dA3 * x.A1⁻¹ * x.A2
      + x.A3 * x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2
      - x.A3 * x.A1⁻¹ * dA2
  (dCtop, (dD, (dA1, (dA3, (dF2, (dF3, dC))))))

/-- Full formal tangent formula of the inverse p. 13 one-step coordinate
change. -/
def productReductionStepFormalJacobianInverseFormula
    (y : ProductReductionStepChartCoordinates ρ π μ ν K)
    (v : ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)) :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) :=
  let dCtop : Matrix ρ ρ K := v.1
  let dD : Matrix π μ K := v.2.1
  let dA1 : Matrix ρ ρ K := v.2.2.1
  let dA3 : Matrix μ ρ K := v.2.2.2.1
  let dF2 : Matrix ρ ν K := v.2.2.2.2.1
  let dF3 : Matrix π ρ K := v.2.2.2.2.2.1
  let dC : Matrix μ ν K := v.2.2.2.2.2.2
  let dC1 : Matrix ρ ρ K :=
    dCtop * y.A1⁻¹ - y.Ctop * y.A1⁻¹ * dA1 * y.A1⁻¹
  let dF3old : Matrix π ρ K :=
    dF3
      + dD * y.A3 * y.Ctop⁻¹
      + y.D * dA3 * y.Ctop⁻¹
      - y.D * y.A3 * y.Ctop⁻¹ * dCtop * y.Ctop⁻¹
  let dA2 : Matrix ρ ν K := -dA1 * y.F2 - y.A1 * dF2
  let dA4 : Matrix μ ν K := dC - dA3 * y.F2 - y.A3 * dF2
  (dC1, (dD, (dF3old, (dA1, (dA2, (dA3, dA4))))))

/-- The p. 13 chart base point associated to a raw base point for the formal
tangent calculation. -/
def productReductionStepFormalJacobianChartBase
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    ProductReductionStepChartCoordinates ρ π μ ν K where
  Ctop := x.C1 * x.A1
  D := x.D
  A1 := x.A1
  A3 := x.A3
  F2 := -(x.A1⁻¹ * x.A2)
  F3 := x.F3 - x.D * x.A3 * (x.C1 * x.A1)⁻¹
  C := x.A4 - x.A3 * x.A1⁻¹ * x.A2

@[simp]
theorem productReductionStepFormalJacobianChartBase_Ctop
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    (productReductionStepFormalJacobianChartBase
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x).Ctop =
      x.C1 * x.A1 := rfl

@[simp]
theorem productReductionStepFormalJacobianChartBase_D
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    (productReductionStepFormalJacobianChartBase
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x).D =
      x.D := rfl

@[simp]
theorem productReductionStepFormalJacobianChartBase_A1
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    (productReductionStepFormalJacobianChartBase
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x).A1 =
      x.A1 := rfl

@[simp]
theorem productReductionStepFormalJacobianChartBase_A3
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    (productReductionStepFormalJacobianChartBase
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x).A3 =
      x.A3 := rfl

@[simp]
theorem productReductionStepFormalJacobianChartBase_F2
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    (productReductionStepFormalJacobianChartBase
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x).F2 =
      -(x.A1⁻¹ * x.A2) := rfl

@[simp]
theorem productReductionStepFormalJacobianChartBase_F3
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    (productReductionStepFormalJacobianChartBase
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x).F3 =
      x.F3 - x.D * x.A3 * (x.C1 * x.A1)⁻¹ := rfl

@[simp]
theorem productReductionStepFormalJacobianChartBase_C
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    (productReductionStepFormalJacobianChartBase
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x).C =
      x.A4 - x.A3 * x.A1⁻¹ * x.A2 := rfl

/-- Raw tangent projection to `dC1`. -/
def productReductionStepRawTangent_dC1 :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix ρ ρ K where
  toFun v := v.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Raw tangent projection to `dD`. -/
def productReductionStepRawTangent_dD :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix π μ K where
  toFun v := v.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Raw tangent projection to the old `dF3`. -/
def productReductionStepRawTangent_dF3old :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix π ρ K where
  toFun v := v.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Raw tangent projection to `dA1`. -/
def productReductionStepRawTangent_dA1 :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix ρ ρ K where
  toFun v := v.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Raw tangent projection to `dA2`. -/
def productReductionStepRawTangent_dA2 :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix ρ ν K where
  toFun v := v.2.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Raw tangent projection to `dA3`. -/
def productReductionStepRawTangent_dA3 :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix μ ρ K where
  toFun v := v.2.2.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Raw tangent projection to `dA4`. -/
def productReductionStepRawTangent_dA4 :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix μ ν K where
  toFun v := v.2.2.2.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Chart tangent projection to `dCtop`. -/
def productReductionStepChartTangent_dCtop :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix ρ ρ K where
  toFun v := v.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Chart tangent projection to `dD`. -/
def productReductionStepChartTangent_dD :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix π μ K where
  toFun v := v.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Chart tangent projection to `dA1`. -/
def productReductionStepChartTangent_dA1 :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix ρ ρ K where
  toFun v := v.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Chart tangent projection to `dA3`. -/
def productReductionStepChartTangent_dA3 :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix μ ρ K where
  toFun v := v.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Chart tangent projection to `dF2`. -/
def productReductionStepChartTangent_dF2 :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix ρ ν K where
  toFun v := v.2.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Chart tangent projection to `dF3`. -/
def productReductionStepChartTangent_dF3 :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix π ρ K where
  toFun v := v.2.2.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Chart tangent projection to `dC`. -/
def productReductionStepChartTangent_dC :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix μ ν K where
  toFun v := v.2.2.2.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `dCtop` component of the full p. 13 formal tangent map. -/
def productReductionStepFormalJacobian_dCtop
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix ρ ρ K :=
  (mulRightLinearMap ρ K x.A1).comp
      (productReductionStepRawTangent_dC1 (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))
    + (mulLeftLinearMap ρ K x.C1).comp
      (productReductionStepRawTangent_dA1 (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))

/-- `dF2` component of the full p. 13 formal tangent map. -/
def productReductionStepFormalJacobian_dF2
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix ρ ν K :=
  (mulRightLinearMap ρ K x.A2).comp
      ((mulRightLinearMap ρ K x.A1⁻¹).comp
        ((mulLeftLinearMap ρ K x.A1⁻¹).comp
          (productReductionStepRawTangent_dA1
            (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))))
    - (mulLeftLinearMap ν K x.A1⁻¹).comp
      (productReductionStepRawTangent_dA2 (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))

/-- `dF3` component of the full p. 13 formal tangent map. -/
def productReductionStepFormalJacobian_dF3
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix π ρ K :=
  let Ctop : Matrix ρ ρ K := x.C1 * x.A1
  productReductionStepRawTangent_dF3old (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)
    - (mulRightLinearMap π K Ctop⁻¹).comp
      ((mulRightLinearMap π K x.A3).comp
        (productReductionStepRawTangent_dD
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)))
    - (mulRightLinearMap π K Ctop⁻¹).comp
      ((mulLeftLinearMap ρ K x.D).comp
        (productReductionStepRawTangent_dA3
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)))
    + (mulRightLinearMap π K Ctop⁻¹).comp
      ((mulLeftLinearMap ρ K (x.D * x.A3 * Ctop⁻¹)).comp
        (productReductionStepFormalJacobian_dCtop
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x))

/-- `dC` component of the full p. 13 formal tangent map. -/
def productReductionStepFormalJacobian_dC
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix μ ν K :=
  let leftA3 : Matrix μ ρ K := x.A3 * x.A1⁻¹
  productReductionStepRawTangent_dA4 (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)
    - (mulRightLinearMap μ K x.A2).comp
      ((mulRightLinearMap μ K x.A1⁻¹).comp
        (productReductionStepRawTangent_dA3
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)))
    + (mulRightLinearMap μ K x.A2).comp
      ((mulRightLinearMap μ K x.A1⁻¹).comp
        ((mulLeftLinearMap ρ K leftA3).comp
          (productReductionStepRawTangent_dA1
            (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))))
    - (mulLeftLinearMap ν K leftA3).comp
      (productReductionStepRawTangent_dA2 (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))

/-- Bundled full formal tangent map for the p. 13 one-step coordinate change. -/
def productReductionStepFormalJacobian
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) :=
  (productReductionStepFormalJacobian_dCtop
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x).prod
    ((productReductionStepRawTangent_dD
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)).prod
      ((productReductionStepRawTangent_dA1
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)).prod
        ((productReductionStepRawTangent_dA3
            (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)).prod
          ((productReductionStepFormalJacobian_dF2
              (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x).prod
            ((productReductionStepFormalJacobian_dF3
                (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x).prod
              (productReductionStepFormalJacobian_dC
                (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x))))))

@[simp]
theorem productReductionStepFormalJacobian_apply
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (v : ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)) :
    productReductionStepFormalJacobian (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x v =
      productReductionStepFormalJacobianFormula
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x v := by
  rcases v with ⟨dC1, dD, dF3old, dA1, dA2, dA3, dA4⟩
  simp [productReductionStepFormalJacobian, productReductionStepFormalJacobian_dCtop,
    productReductionStepFormalJacobian_dF2, productReductionStepFormalJacobian_dF3,
    productReductionStepFormalJacobian_dC, productReductionStepFormalJacobianFormula,
    productReductionStepRawTangent_dC1, productReductionStepRawTangent_dD,
    productReductionStepRawTangent_dF3old, productReductionStepRawTangent_dA1,
    productReductionStepRawTangent_dA2, productReductionStepRawTangent_dA3,
    productReductionStepRawTangent_dA4, Matrix.mul_assoc]

/-- `dC1` component of the inverse full p. 13 formal tangent map. -/
def productReductionStepFormalJacobianInverse_dC1
    (y : ProductReductionStepChartCoordinates ρ π μ ν K) :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix ρ ρ K :=
  (mulRightLinearMap ρ K y.A1⁻¹).comp
      (productReductionStepChartTangent_dCtop
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))
    - (mulRightLinearMap ρ K y.A1⁻¹).comp
      ((mulLeftLinearMap ρ K (y.Ctop * y.A1⁻¹)).comp
        (productReductionStepChartTangent_dA1
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)))

/-- Old `dF3` component of the inverse full p. 13 formal tangent map. -/
def productReductionStepFormalJacobianInverse_dF3old
    (y : ProductReductionStepChartCoordinates ρ π μ ν K) :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix π ρ K :=
  productReductionStepChartTangent_dF3 (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)
    + (mulRightLinearMap π K y.Ctop⁻¹).comp
      ((mulRightLinearMap π K y.A3).comp
        (productReductionStepChartTangent_dD
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)))
    + (mulRightLinearMap π K y.Ctop⁻¹).comp
      ((mulLeftLinearMap ρ K y.D).comp
        (productReductionStepChartTangent_dA3
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)))
    - (mulRightLinearMap π K y.Ctop⁻¹).comp
      ((mulLeftLinearMap ρ K (y.D * y.A3 * y.Ctop⁻¹)).comp
        (productReductionStepChartTangent_dCtop
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)))

/-- `dA2` component of the inverse full p. 13 formal tangent map. -/
def productReductionStepFormalJacobianInverse_dA2
    (y : ProductReductionStepChartCoordinates ρ π μ ν K) :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix ρ ν K :=
  - (mulRightLinearMap ρ K y.F2).comp
      (productReductionStepChartTangent_dA1
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))
    - (mulLeftLinearMap ν K y.A1).comp
      (productReductionStepChartTangent_dF2
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))

/-- `dA4` component of the inverse full p. 13 formal tangent map. -/
def productReductionStepFormalJacobianInverse_dA4
    (y : ProductReductionStepChartCoordinates ρ π μ ν K) :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      Matrix μ ν K :=
  productReductionStepChartTangent_dC (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)
    - (mulRightLinearMap μ K y.F2).comp
      (productReductionStepChartTangent_dA3
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))
    - (mulLeftLinearMap ν K y.A3).comp
      (productReductionStepChartTangent_dF2
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))

/-- Bundled inverse full formal tangent map for the p. 13 one-step coordinate
change. -/
def productReductionStepFormalJacobianInverse
    (y : ProductReductionStepChartCoordinates ρ π μ ν K) :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) :=
  (productReductionStepFormalJacobianInverse_dC1
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) y).prod
    ((productReductionStepChartTangent_dD
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)).prod
      ((productReductionStepFormalJacobianInverse_dF3old
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) y).prod
        ((productReductionStepChartTangent_dA1
            (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)).prod
          ((productReductionStepFormalJacobianInverse_dA2
              (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) y).prod
            ((productReductionStepChartTangent_dA3
                (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)).prod
              (productReductionStepFormalJacobianInverse_dA4
                (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) y))))))

@[simp]
theorem productReductionStepFormalJacobianInverse_apply
    (y : ProductReductionStepChartCoordinates ρ π μ ν K)
    (v : ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)) :
    productReductionStepFormalJacobianInverse
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) y v =
      productReductionStepFormalJacobianInverseFormula
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) y v := by
  rcases v with ⟨dCtop, dD, dA1, dA3, dF2, dF3, dC⟩
  simp [productReductionStepFormalJacobianInverse,
    productReductionStepFormalJacobianInverse_dC1,
    productReductionStepFormalJacobianInverse_dF3old,
    productReductionStepFormalJacobianInverse_dA2,
    productReductionStepFormalJacobianInverse_dA4,
    productReductionStepFormalJacobianInverseFormula,
    productReductionStepChartTangent_dCtop, productReductionStepChartTangent_dD,
    productReductionStepChartTangent_dA1, productReductionStepChartTangent_dA3,
    productReductionStepChartTangent_dF2, productReductionStepChartTangent_dF3,
    productReductionStepChartTangent_dC, Matrix.mul_assoc]

/-- The inverse formal tangent formula recovers the raw tangent formula at the
raw-derived chart base point. -/
theorem productReductionStepFormalJacobianInverseFormula_formula_chartBase
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hC1 : IsUnit x.C1.det) (hA1 : IsUnit x.A1.det)
    (v : ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)) :
    productReductionStepFormalJacobianInverseFormula
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)
        (productReductionStepFormalJacobianChartBase
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x)
        (productReductionStepFormalJacobianFormula
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x v) = v := by
  have hCtop : IsUnit (x.C1 * x.A1).det := by
    simpa [Matrix.det_mul] using hC1.mul hA1
  rcases v with ⟨dC1, dD, dF3old, dA1, dA2, dA3, dA4⟩
  apply Prod.ext
  · change
      (dC1 * x.A1 + x.C1 * dA1) * x.A1⁻¹ -
          (x.C1 * x.A1) * x.A1⁻¹ * dA1 * x.A1⁻¹ =
        dC1
    have hleft :
        (dC1 * x.A1 + x.C1 * dA1) * x.A1⁻¹ =
          dC1 + x.C1 * dA1 * x.A1⁻¹ := by
      simp [Matrix.add_mul, Matrix.mul_assoc, hA1]
    have hright :
        (x.C1 * x.A1) * x.A1⁻¹ * dA1 * x.A1⁻¹ =
          x.C1 * dA1 * x.A1⁻¹ := by
      simp [Matrix.mul_assoc, hA1]
    rw [hleft, hright]
    abel
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · change
          dF3old
              - dD * x.A3 * (x.C1 * x.A1)⁻¹
              - x.D * dA3 * (x.C1 * x.A1)⁻¹
              + x.D * x.A3 * (x.C1 * x.A1)⁻¹ *
                  (dC1 * x.A1 + x.C1 * dA1) * (x.C1 * x.A1)⁻¹
              + dD * x.A3 * (x.C1 * x.A1)⁻¹
              + x.D * dA3 * (x.C1 * x.A1)⁻¹
              - x.D * x.A3 * (x.C1 * x.A1)⁻¹ *
                  (dC1 * x.A1 + x.C1 * dA1) * (x.C1 * x.A1)⁻¹ =
            dF3old
        abel
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · change
              -dA1 * (-(x.A1⁻¹ * x.A2)) -
                  x.A1 * (x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2 - x.A1⁻¹ * dA2) =
                dA2
            have hterm1 :
                -dA1 * (-(x.A1⁻¹ * x.A2)) = dA1 * x.A1⁻¹ * x.A2 := by
              ext i j
              simp [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
            have hterm2 :
                x.A1 * (x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2 - x.A1⁻¹ * dA2) =
                  dA1 * x.A1⁻¹ * x.A2 - dA2 := by
              rw [Matrix.mul_sub]
              congr 1 <;> simp [Matrix.mul_assoc, hA1]
            rw [hterm1, hterm2]
            abel
          · apply Prod.ext
            · rfl
            · change
                dA4
                    - dA3 * x.A1⁻¹ * x.A2
                    + x.A3 * x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2
                    - x.A3 * x.A1⁻¹ * dA2
                    - dA3 * (-(x.A1⁻¹ * x.A2))
                    - x.A3 * (x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2 - x.A1⁻¹ * dA2) =
                  dA4
              have hterm1 :
                  dA3 * (-(x.A1⁻¹ * x.A2)) =
                    -(dA3 * x.A1⁻¹ * x.A2) := by
                calc
                  dA3 * (-(x.A1⁻¹ * x.A2)) = -(dA3 * (x.A1⁻¹ * x.A2)) := by
                    rw [Matrix.mul_neg]
                  _ = -(dA3 * x.A1⁻¹ * x.A2) := by
                    rw [Matrix.mul_assoc]
              have hterm2 :
                  x.A3 * (x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2 - x.A1⁻¹ * dA2) =
                    x.A3 * x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2 -
                      x.A3 * x.A1⁻¹ * dA2 := by
                rw [Matrix.mul_sub]
                congr 1 <;> simp [Matrix.mul_assoc]
              rw [hterm1, hterm2]
              abel

/-- The raw formal tangent formula recovers the chart tangent formula after
applying the inverse formula at the raw-derived chart base point. -/
theorem productReductionStepFormalJacobianFormula_inverseFormula_chartBase
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hC1 : IsUnit x.C1.det) (hA1 : IsUnit x.A1.det)
    (v : ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)) :
    productReductionStepFormalJacobianFormula
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x
        (productReductionStepFormalJacobianInverseFormula
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)
          (productReductionStepFormalJacobianChartBase
            (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x) v) = v := by
  have _hCtop : IsUnit (x.C1 * x.A1).det := by
    simpa [Matrix.det_mul] using hC1.mul hA1
  rcases v with ⟨dCtop, dD, dA1, dA3, dF2, dF3, dC⟩
  have hCtopLinear :
      (dCtop * x.A1⁻¹ -
            (x.C1 * x.A1) * x.A1⁻¹ * dA1 * x.A1⁻¹) *
          x.A1 + x.C1 * dA1 =
        dCtop := by
    have hleft :
        (dCtop * x.A1⁻¹ -
              (x.C1 * x.A1) * x.A1⁻¹ * dA1 * x.A1⁻¹) *
            x.A1 =
          dCtop - x.C1 * dA1 := by
      rw [Matrix.sub_mul]
      congr 1 <;> simp [Matrix.mul_assoc, hA1]
    rw [hleft]
    abel
  have hdA1F2 :
      -dA1 * (-(x.A1⁻¹ * x.A2)) = dA1 * x.A1⁻¹ * x.A2 := by
    ext i j
    simp [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hdA2raw :
      -dA1 * (-(x.A1⁻¹ * x.A2)) - x.A1 * dF2 =
        dA1 * x.A1⁻¹ * x.A2 - x.A1 * dF2 := by
    rw [hdA1F2]
  have hdA3F2 :
      dA3 * (-(x.A1⁻¹ * x.A2)) = -(dA3 * x.A1⁻¹ * x.A2) := by
    ext i j
    simp [Matrix.mul_neg, Matrix.mul_assoc]
  apply Prod.ext
  · change
      (dCtop * x.A1⁻¹ -
            (x.C1 * x.A1) * x.A1⁻¹ * dA1 * x.A1⁻¹) *
          x.A1 + x.C1 * dA1 =
        dCtop
    exact hCtopLinear
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · change
              x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2 -
                  x.A1⁻¹ *
                    (-dA1 * (-(x.A1⁻¹ * x.A2)) - x.A1 * dF2) =
                dF2
            have hterm :
                x.A1⁻¹ *
                    (-dA1 * (-(x.A1⁻¹ * x.A2)) - x.A1 * dF2) =
                  x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2 - dF2 := by
              rw [hdA2raw, Matrix.mul_sub]
              congr 1 <;> simp [Matrix.mul_assoc, hA1]
            rw [hterm]
            abel
          · apply Prod.ext
            · change
                dF3
                    + dD * x.A3 * (x.C1 * x.A1)⁻¹
                    + x.D * dA3 * (x.C1 * x.A1)⁻¹
                    - x.D * x.A3 * (x.C1 * x.A1)⁻¹ *
                        dCtop * (x.C1 * x.A1)⁻¹
                    - dD * x.A3 * (x.C1 * x.A1)⁻¹
                    - x.D * dA3 * (x.C1 * x.A1)⁻¹
                    + x.D * x.A3 * (x.C1 * x.A1)⁻¹ *
                        ((dCtop * x.A1⁻¹ -
                              (x.C1 * x.A1) * x.A1⁻¹ *
                                dA1 * x.A1⁻¹) *
                            x.A1 + x.C1 * dA1) *
                          (x.C1 * x.A1)⁻¹ =
                  dF3
              rw [hCtopLinear]
              abel
            · change
                dC
                    - dA3 * (-(x.A1⁻¹ * x.A2))
                    - x.A3 * dF2
                    - dA3 * x.A1⁻¹ * x.A2
                    + x.A3 * x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2
                    - x.A3 * x.A1⁻¹ *
                        (-dA1 * (-(x.A1⁻¹ * x.A2)) - x.A1 * dF2) =
                  dC
              have hterm :
                  x.A3 * x.A1⁻¹ *
                      (-dA1 * (-(x.A1⁻¹ * x.A2)) - x.A1 * dF2) =
                    x.A3 * x.A1⁻¹ * dA1 * x.A1⁻¹ * x.A2 -
                      x.A3 * dF2 := by
                rw [hdA2raw, Matrix.mul_sub]
                congr 1 <;> simp [Matrix.mul_assoc, hA1]
              rw [hdA3F2, hterm]
              abel

/-- The full p. 13 formal tangent map is a linear equivalence from raw tangent
coordinates to chart tangent coordinates at the raw-derived chart base point. -/
def productReductionStepFormalJacobianEquiv
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hC1 : IsUnit x.C1.det) (hA1 : IsUnit x.A1.det) :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) ≃ₗ[K]
      ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) :=
  LinearEquiv.ofLinear
    (productReductionStepFormalJacobian
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x)
    (productReductionStepFormalJacobianInverse
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)
      (productReductionStepFormalJacobianChartBase
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x))
    (by
      apply LinearMap.ext
      intro v
      simp [productReductionStepFormalJacobianFormula_inverseFormula_chartBase,
        hC1, hA1])
    (by
      apply LinearMap.ext
      intro v
      simp [productReductionStepFormalJacobianInverseFormula_formula_chartBase,
        hC1, hA1])

@[simp]
theorem productReductionStepFormalJacobianEquiv_apply
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hC1 : IsUnit x.C1.det) (hA1 : IsUnit x.A1.det)
    (v : ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)) :
    productReductionStepFormalJacobianEquiv
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x hC1 hA1 v =
      productReductionStepFormalJacobian
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x v :=
  rfl

@[simp]
theorem productReductionStepFormalJacobianEquiv_symm_apply
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hC1 : IsUnit x.C1.det) (hA1 : IsUnit x.A1.det)
    (v : ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)) :
    (productReductionStepFormalJacobianEquiv
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x hC1 hA1).symm v =
      productReductionStepFormalJacobianInverse
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)
        (productReductionStepFormalJacobianChartBase
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x) v :=
  rfl

/-- Reorder chart tangent coordinates into the raw-shaped order.

The full p. 13 formal Jacobian naturally maps raw order
`(C1,D,F3old,A1,A2,A3,A4)` to chart order `(Ctop,D,A1,A3,F2,F3,C)`.  A
determinant statement must first compose with this finite coordinate
permutation, so that the codomain has the raw-shaped order
`(Ctop,D,F3,A1,F2,A3,C)`. -/
def productReductionStepChartTangentRawOrderEquiv :
    ProductReductionStepChartTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) ≃ₗ[K]
      ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) where
  toFun v :=
    (v.1,
      (v.2.1,
        (v.2.2.2.2.2.1,
          (v.2.2.1,
            (v.2.2.2.2.1,
              (v.2.2.2.1, v.2.2.2.2.2.2))))))
  invFun v :=
    (v.1,
      (v.2.1,
        (v.2.2.2.1,
          (v.2.2.2.2.2.1,
            (v.2.2.2.2.1,
              (v.2.2.1, v.2.2.2.2.2.2))))))
  map_add' v w := by
    rcases v with ⟨dCtop, dD, dA1, dA3, dF2, dF3, dC⟩
    rcases w with ⟨eCtop, eD, eA1, eA3, eF2, eF3, eC⟩
    rfl
  map_smul' a v := by
    rcases v with ⟨dCtop, dD, dA1, dA3, dF2, dF3, dC⟩
    rfl
  left_inv v := by
    rcases v with ⟨dCtop, dD, dA1, dA3, dF2, dF3, dC⟩
    rfl
  right_inv v := by
    rcases v with ⟨dCtop, dD, dF3, dA1, dF2, dA3, dC⟩
    rfl

/-- The full p. 13 formal tangent map with chart output reordered into the
raw-shaped tangent order. -/
def productReductionStepFormalJacobianRawOrder
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) →ₗ[K]
      ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) :=
  (productReductionStepChartTangentRawOrderEquiv
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)).toLinearMap.comp
    (productReductionStepFormalJacobian
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x)

@[simp]
theorem productReductionStepFormalJacobianRawOrder_apply
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (v : ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)) :
    productReductionStepFormalJacobianRawOrder
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x v =
      productReductionStepChartTangentRawOrderEquiv
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)
        (productReductionStepFormalJacobian
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x v) :=
  rfl

/-- The raw-order full p. 13 formal tangent map is a linear automorphism on
the determinant chart. -/
def productReductionStepFormalJacobianRawOrderEquiv
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hC1 : IsUnit x.C1.det) (hA1 : IsUnit x.A1.det) :
    ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) ≃ₗ[K]
      ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) :=
  (productReductionStepFormalJacobianEquiv
    (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x hC1 hA1).trans
    (productReductionStepChartTangentRawOrderEquiv
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K))

@[simp]
theorem productReductionStepFormalJacobianRawOrderEquiv_apply
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hC1 : IsUnit x.C1.det) (hA1 : IsUnit x.A1.det)
    (v : ProductReductionStepRawTangent (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K)) :
    productReductionStepFormalJacobianRawOrderEquiv
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x hC1 hA1 v =
      productReductionStepFormalJacobianRawOrder
        (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x v :=
  rfl

/-- The raw-order full p. 13 formal Jacobian determinant is a unit on the
determinant chart.

This is a finite formal determinant statement. It is not an analytic
change-of-variables theorem or source-measure pushforward statement. -/
theorem productReductionStepFormalJacobianRawOrder_det_isUnit
    [Finite π] [Finite ν]
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hC1 : IsUnit x.C1.det) (hA1 : IsUnit x.A1.det) :
    IsUnit
      (LinearMap.det
        (productReductionStepFormalJacobianRawOrder
          (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x)) := by
  let _ : Fintype π := Fintype.ofFinite π
  let _ : Fintype ν := Fintype.ofFinite ν
  exact LinearEquiv.isUnit_det'
    (productReductionStepFormalJacobianRawOrderEquiv
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) (K := K) x hC1 hA1)

end ProductStepFull

end Aoyagi
end DLN
end DLNFibre
