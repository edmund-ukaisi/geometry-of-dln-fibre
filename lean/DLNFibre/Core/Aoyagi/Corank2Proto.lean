import DLNFibre.Core.Aoyagi.IdealInvariance
import DLNFibre.Core.Aoyagi.BlockBlowup
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# `Core.Aoyagi.Corank2Proto` — PROTOTYPE (measurement, not value path)

Renders ONE corank-2 matrix-ideal Schur-clearing step for the instance
`M=(3,3,4)`, `L=2`, branch `t=(1,0)` (the coupled-only corank-2 minimiser). This is the DECISION-GATE
measurement for the re-architecture (matrix-ideal route vs geometric-substitution fold): how expensive
is the Lean "cast tax" for the dependent-dim block-matrix Schur products?

Contract: `expeditions/2026-07-17-aoyagi-engine/threads/L4-case1-core/corank2-cert/certificate.md`.
Math source of truth: `cert_334_corank2.py` (Gröbner-verified, exit 0). This file RENDERS that; it
does not re-derive it.

**Scope.** ONE step only. NOT the R1 radial recursion, NOT the full resolution. All identities are
sorry-free. This is a Core, network-free measurement module; it is NOT on any headline's value path.
-/

open Matrix

namespace DLNFibre.Core.Aoyagi.Corank2Proto

/-! ## §2 [QP] — the unipotent-polynomial Schur cofactors (symbolic, over a general comm ring)

The chart coordinates enter as FREE ring elements, so `Q1·C1·Q2 = diag(1,Δ)` is the genuine symbolic
matrix identity (not an integer `decide`). This measures the `Matrix.ext` + `Fin.sum_univ_three` +
`ring` tax at 3×3 with symbolic entries — the certificate's `[QP]` item. -/

variable {R : Type*} [CommRing R]

/-- `C1 = C^(1)` on the normalized pivot chart (pivot `c11 ≡ 1`), certificate `[QP]`. -/
def C1 (c12a c12b c21a c21b m11 m12 m21 m22 : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, c12a, c12b; c21a, m11, m12; c21b, m21, m22]

/-- Row shear `Q1 = [[1,0,0],[-c21a,1,0],[-c21b,0,1]]` (unipotent-polynomial). -/
def Q1 (c21a c21b : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0; -c21a, 1, 0; -c21b, 0, 1]

/-- Column shear `Q2 = [[1,-c12a,-c12b],[0,1,0],[0,0,1]]` (unipotent-polynomial). -/
def Q2 (c12a c12b : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, -c12a, -c12b; 0, 1, 0; 0, 0, 1]

/-- Polynomial inverse `Q1⁻¹ = [[1,0,0],[c21a,1,0],[c21b,0,1]]`. -/
def Q1inv (c21a c21b : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0; c21a, 1, 0; c21b, 0, 1]

/-- Polynomial inverse `Q2⁻¹ = [[1,c12a,c12b],[0,1,0],[0,0,1]]`. -/
def Q2inv (c12a c12b : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, c12a, c12b; 0, 1, 0; 0, 0, 1]

/-- The coupled Schur complement `Δ = C22 − C21·C12` (2×2). -/
def Delta (c12a c12b c21a c21b m11 m12 m21 m22 : R) : Matrix (Fin 2) (Fin 2) R :=
  !![m11 - c12a * c21a, m12 - c12b * c21a; m21 - c12a * c21b, m22 - c12b * c21b]

/-- `diag(1, Δ)` as a 3×3 matrix (the peeled `C1`). -/
def diag1Delta (c12a c12b c21a c21b m11 m12 m21 m22 : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, m11 - c12a * c21a, m12 - c12b * c21a;
     0, m21 - c12a * c21b, m22 - c12b * c21b]

/-- **[QP] the block elimination** `Q1·C1·Q2 = diag(1, Δ)` (symbolic, exact). -/
theorem Q1_C1_Q2_eq_diag (c12a c12b c21a c21b m11 m12 m21 m22 : R) :
    Q1 c21a c21b * C1 c12a c12b c21a c21b m11 m12 m21 m22 * Q2 c12a c12b
      = diag1Delta c12a c12b c21a c21b m11 m12 m21 m22 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q1, C1, Q2, diag1Delta, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- `det Q1 = 1` (unimodular). -/
theorem det_Q1 (c21a c21b : R) : (Q1 c21a c21b).det = 1 := by
  simp [Q1, Matrix.det_fin_three]

/-- `det Q2 = 1` (unimodular). -/
theorem det_Q2 (c12a c12b : R) : (Q2 c12a c12b).det = 1 := by
  simp [Q2, Matrix.det_fin_three]

/-- `Q1⁻¹` is a genuine left inverse: `Q1inv · Q1 = 1`. -/
theorem Q1inv_mul_Q1 (c21a c21b : R) :
    Q1inv c21a c21b * Q1 c21a c21b = (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q1inv, Q1, Matrix.mul_apply, Fin.sum_univ_three]

/-- `Q2⁻¹ · Q2 = 1`. -/
theorem Q2inv_mul_Q2 (c12a c12b : R) :
    Q2inv c12a c12b * Q2 c12a c12b = (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q2inv, Q2, Matrix.mul_apply, Fin.sum_univ_three]

/-- **Reconstruction** `Q1⁻¹ · diag(1,Δ) · Q2⁻¹ = C1` (certificate `[QP]`). -/
theorem reconstruct_C1 (c12a c12b c21a c21b m11 m12 m21 m22 : R) :
    Q1inv c21a c21b * diag1Delta c12a c12b c21a c21b m11 m12 m21 m22 * Q2inv c12a c12b
      = C1 c12a c12b c21a c21b m11 m12 m21 m22 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q1inv, Q2inv, diag1Delta, C1, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- `Q2 · Q2⁻¹ = 1` (needed for the backward direction). -/
theorem Q2_mul_Q2inv (c12a c12b : R) :
    Q2 c12a c12b * Q2inv c12a c12b = (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q2inv, Q2, Matrix.mul_apply, Fin.sum_univ_three]

/-! ## §3 [ML] — the multi-layer reassociation (the cast-tax measurement)

The load-bearing product `peeled = diag(1,Δ)·(Q2⁻¹·C2)` and the two matrix-level ideal identities
`P = Q1⁻¹·peeled` (forward) and `peeled = Q1·P` (backward). These reduce to §2 + associativity: the
`[ML]` reassociation tax appears here and NOWHERE else, as `(A·B)·C ↔ A·(B·C)` steps. -/

/-- The banked dependent-dim reassociation idiom `(A·B)·C = A·(B·C)` as a fully-applied term. This is
the certificate `[ML]` mitigation: polymorphic in the index types, so it fires at concrete AND opaque
(`Fin (M−J)`) widths, where `rw [Matrix.mul_assoc]` fails the dependent `HMul` higher-order match. -/
theorem mul_three_reassoc {p q r s : Type*} [Fintype q] [Fintype r]
    (A : Matrix p q R) (B : Matrix q r R) (C : Matrix r s R) :
    A * B * C = A * (B * C) := Matrix.mul_assoc A B C

/-- **Dependent-width sample.** The recursion carries residual blocks of width `Fin (M − J)`. The
reassociation fires via the fully-applied term at that opaque width — the `[ML]` idiom, confirmed to
close at a genuinely dependent dimension (not just the concrete `Fin 3`). -/
theorem mul_three_reassoc_depWidth {M J q : ℕ}
    (A : Matrix (Fin (M - J)) (Fin (M - J)) R) (B : Matrix (Fin (M - J)) (Fin (M - J)) R)
    (C : Matrix (Fin (M - J)) (Fin q) R) :
    A * B * C = A * (B * C) := mul_three_reassoc A B C

/-- The product `P = C^(1)·C^(2)` (the 12 generators), certificate `[ML]`. -/
def Pmat (c12a c12b c21a c21b m11 m12 m21 m22 : R) (C2 : Matrix (Fin 3) (Fin 4) R) :
    Matrix (Fin 3) (Fin 4) R :=
  C1 c12a c12b c21a c21b m11 m12 m21 m22 * C2

/-- The peeled product `peeled = diag(1,Δ)·(Q2⁻¹·C2)`, certificate `[ML]` step 2 (the reassociation
point). -/
def peeled (c12a c12b c21a c21b m11 m12 m21 m22 : R) (C2 : Matrix (Fin 3) (Fin 4) R) :
    Matrix (Fin 3) (Fin 4) R :=
  diag1Delta c12a c12b c21a c21b m11 m12 m21 m22 * (Q2inv c12a c12b * C2)

/-- **[I⇒] forward matrix identity** `P = Q1⁻¹·peeled`: reconstruction `Q1⁻¹·diag(1,Δ)·Q2⁻¹ = C1`
followed by the `[ML]` reassociation (twice). -/
theorem Pmat_eq_Q1inv_peeled (c12a c12b c21a c21b m11 m12 m21 m22 : R)
    (C2 : Matrix (Fin 3) (Fin 4) R) :
    Pmat c12a c12b c21a c21b m11 m12 m21 m22 C2
      = Q1inv c21a c21b * peeled c12a c12b c21a c21b m11 m12 m21 m22 C2 := by
  rw [Pmat, peeled, ← reconstruct_C1 c12a c12b c21a c21b m11 m12 m21 m22,
    Matrix.mul_assoc, Matrix.mul_assoc]

/-- **[I⇐] backward matrix identity** `peeled = Q1·P`: `diag(1,Δ) = Q1·C1·Q2`, then reassociate to
expose `Q2·Q2⁻¹ = 1`. -/
theorem peeled_eq_Q1_Pmat (c12a c12b c21a c21b m11 m12 m21 m22 : R)
    (C2 : Matrix (Fin 3) (Fin 4) R) :
    peeled c12a c12b c21a c21b m11 m12 m21 m22 C2
      = Q1 c21a c21b * Pmat c12a c12b c21a c21b m11 m12 m21 m22 C2 := by
  rw [peeled, Pmat, ← Q1_C1_Q2_eq_diag c12a c12b c21a c21b m11 m12 m21 m22]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Q2 c12a c12b) (Q2inv c12a c12b) C2, Q2_mul_Q2inv, Matrix.one_mul]

end DLNFibre.Core.Aoyagi.Corank2Proto
