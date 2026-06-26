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

end Aoyagi
end DLN
end DLNFibre
