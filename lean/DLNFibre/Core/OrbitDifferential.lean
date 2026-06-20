import DLNFibre.Core.DeformationExt
import Mathlib.Algebra.DualNumber
import Mathlib.Data.Matrix.DualNumber

/-!
# `DLNFibre.Core.OrbitDifferential` — `dμ_M at e = deformationδ M M` (dual-number form)

The first-order ("identity-point") differential of the `G_d`-orbit map `μ_M : P ↦ (P_{i+1} M_i
P_i⁻¹)_i` equals the deformation coboundary `δ⁰ = deformationδ M M`. Modelling the group element at the
identity in tangent direction `φ` by `P_v = 1 + ε φ_v` over the **dual numbers** `DualNumber k =
k[ε]/(ε²)`, the ε-part of `P_{i+1} M_i P_i⁻¹` is exactly `(deformationδ M M φ)_i = φ_{i+1} M_i −
M_i φ_i`:

> `(1 + ε φ_{i+1}) · M_i · (1 − ε φ_i) = M_i + ε · (deformationδ M M φ)_i`.

This is the structural `dμ_e = δ⁰` certificate (thread 36 §2), char-free. It is the geometric heart of
both the A4.3 differential-rank identity (the orbit-map Jacobian at the identity = `δ⁰`) and the A6.1
reverse-inequality tide's R2★ (the first-order orbit-tangent inclusion `D_{δ⁰φ} f = 0` for `f` in the
orbit's vanishing ideal — the dual-number `1 + εφ` curve). `(1 − ε φ)` is the inverse of `(1 + ε φ)`
(`one_add_eps_mul_one_sub_eps`), modelling `P⁻¹` to first order.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix DualNumber TrivSqZeroExt

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- The entrywise lift of a `k`-matrix to `DualNumber k` (the constant / `fst` part). -/
noncomputable def liftMat {a b : ℕ} (A : Matrix (Fin a) (Fin b) k) :
    Matrix (Fin a) (Fin b) (DualNumber k) :=
  A.map (algebraMap k (DualNumber k))

/-- `liftMat` is multiplicative (the entrywise lift is a ring-hom map). -/
@[simp] theorem liftMat_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) k)
    (B : Matrix (Fin b) (Fin c) k) : liftMat (A * B) = liftMat A * liftMat B := by
  rw [liftMat, liftMat, liftMat, ← Matrix.map_mul]

/-- `liftMat` is additive on differences. -/
theorem liftMat_sub {a b : ℕ} (A B : Matrix (Fin a) (Fin b) k) :
    liftMat (A - B) = liftMat A - liftMat B := by
  rw [liftMat, liftMat, liftMat, Matrix.map_sub _ (map_sub _)]

/-- `liftMat` sends the identity to the identity. -/
theorem liftMat_one {a : ℕ} : liftMat (1 : Matrix (Fin a) (Fin a) k) = 1 := by
  rw [liftMat, Matrix.map_one _ (map_zero _) (map_one _)]

/-- `ε•(liftMat A) * liftMat B = ε • liftMat (A·B)` (the `ε` scalar pulls out of a product). -/
theorem eps_smul_liftMat_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) k)
    (B : Matrix (Fin b) (Fin c) k) :
    ((ε : DualNumber k) • liftMat A) * liftMat B = (ε : DualNumber k) • liftMat (A * B) := by
  rw [Matrix.smul_mul, liftMat_mul]

/-- `liftMat A * (ε•liftMat B) = ε • liftMat (A·B)`. -/
theorem liftMat_mul_eps_smul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) k)
    (B : Matrix (Fin b) (Fin c) k) :
    liftMat A * ((ε : DualNumber k) • liftMat B) = (ε : DualNumber k) • liftMat (A * B) := by
  rw [Matrix.mul_smul, liftMat_mul]

/-- A product of two `ε`-perturbations vanishes (`ε² = 0`): the second-order term drops out. -/
theorem eps_smul_sq {a b c : ℕ} (A : Matrix (Fin a) (Fin b) k) (B : Matrix (Fin b) (Fin c) k) :
    ((ε : DualNumber k) • liftMat A) * ((ε : DualNumber k) • liftMat B) = 0 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show (ε * ε : DualNumber k) = 0 from eps_mul_eps, zero_smul]

/-- **`(1 + ε φ)⁻¹ = 1 − ε φ`** to first order: `(1 + ε φ)·(1 − ε φ) = 1` (the `ε²` term vanishes).
Models the inverse `P_v⁻¹` of the infinitesimal group element `P_v = 1 + ε φ_v` at the identity. -/
theorem one_add_eps_mul_one_sub_eps {a : ℕ} (φ : Matrix (Fin a) (Fin a) k) :
    ((1 : Matrix (Fin a) (Fin a) (DualNumber k)) + (ε : DualNumber k) • liftMat φ)
      * (1 - (ε : DualNumber k) • liftMat φ) = 1 := by
  have hee : ((ε : DualNumber k) • liftMat φ) * ((ε : DualNumber k) • liftMat φ) = 0 :=
    eps_smul_sq φ φ
  rw [Matrix.mul_sub, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hee, add_zero, add_sub_cancel_right]

/-- **`dμ_M at e = deformationδ M M` (dual-number form).** The ε-part of the orbit action
`P_{i+1} M_i P_i⁻¹` at `P_v = 1 + ε φ_v` is exactly the coboundary `(deformationδ M M φ)_i`:

> `(1 + ε φ_{i+1}) · M_i · (1 − ε φ_i) = M_i + ε · (deformationδ M M φ)_i`.

Char-free. The `dμ_e = δ⁰` certificate (thread 36 §2), structural in Lean; reusable by A4.3 and A6.1. -/
theorem orbitAction_eps_eq_deformationδ {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (φ : cochain0 (k := k) d d) (i : Fin N) :
    ((1 : Matrix (Fin (d i.succ)) (Fin (d i.succ)) (DualNumber k))
        + (ε : DualNumber k) • liftMat (φ i.succ)) * liftMat (M i)
      * (1 - (ε : DualNumber k) • liftMat (φ i.castSucc))
      = liftMat (M i) + (ε : DualNumber k) • liftMat (deformationδ M M φ i) := by
  rw [deformationδ_apply, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.add_mul, eps_smul_liftMat_mul, liftMat_mul_eps_smul,
    show ((ε : DualNumber k) • liftMat (φ i.succ * M i))
        * ((ε : DualNumber k) • liftMat (φ i.castSucc)) = 0 from eps_smul_sq _ _,
    liftMat_sub, smul_sub]
  abel

end DLNFibre.Core
