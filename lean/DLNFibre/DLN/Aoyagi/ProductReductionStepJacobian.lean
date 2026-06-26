import DLNFibre.DLN.Aoyagi.ChartTopology
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

end Aoyagi
end DLN
end DLNFibre
