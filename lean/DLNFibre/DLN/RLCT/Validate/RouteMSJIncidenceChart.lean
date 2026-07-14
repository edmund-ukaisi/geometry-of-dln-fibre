import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotBlowup
import Mathlib.Data.Matrix.ColumnRowPartitioned

set_option linter.style.longLine false

/-!
# `RouteMSJIncidenceChart` — Brick D joint-resolution: the minor-chart corank-Gram monomialization

**Thread `genm-sj5-brickdbuild`, aoyagi-full Stage 2.** The load-bearing algebraic identity the
incidence-rank resolution (`genm-incidencepp/incidence-cert.md`) is built around: on the `b×b`-minor chart
`Q_b = D·[I_b | X]` (`D : b×b`, `X : b×d`, `n = b+d`), the corank Gram factors as

    det(Q_b Q_bᵀ) = (det D)² · det(I_b + X Xᵀ).

The rank-drop singularity lives ENTIRELY in `|det D|` (the incidence monomial); `det(I + X Xᵀ) ≥ 1` is a
unit (bounded away from 0), and `X` (the transverse-Schur coordinate) is independent of `D`. This
disjoint-variable factoring is what lets the det-Gram and the transverse Schur monomialize simultaneously
with no blow-up conflict (cert §0, §2). Network-free matrix algebra; sorry-free; axiom-clean.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-- **The column-partitioned Gram** `(fromCols U V)·(fromCols U V)ᵀ = U Uᵀ + V Vᵀ`. The reusable block
identity behind every chart-Gram computation (`transpose_fromCols` + `fromCols_mul_fromRows`). -/
theorem fromCols_mul_transpose {m n₁ n₂ : ℕ} (U : Matrix (Fin m) (Fin n₁) ℝ)
    (V : Matrix (Fin m) (Fin n₂) ℝ) :
    (Matrix.fromCols U V) * (Matrix.fromCols U V)ᵀ = U * Uᵀ + V * Vᵀ := by
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]

/-- **The minor-chart Gram congruence.** For `Q_b = D·[I_b | X]` (`[I_b | X] = fromCols 1 X`), the corank
Gram is the congruence `D·(I + X Xᵀ)·Dᵀ`: the block product `[I|X]·[I|X]ᵀ = I·I + X·Xᵀ = I + X Xᵀ`. -/
theorem chartGram_congr {b d : ℕ} (D : Matrix (Fin b) (Fin b) ℝ) (X : Matrix (Fin b) (Fin d) ℝ) :
    (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X) * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ
      = D * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ) * Dᵀ := by
  have hE : (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)
      * (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ
      = (1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ := by
    have h11 : (1 : Matrix (Fin b) (Fin b) ℝ) * (1 : Matrix (Fin b) (Fin b) ℝ)ᵀ = 1 := by
      rw [Matrix.transpose_one, Matrix.one_mul]
    rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, h11]
  calc (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X) * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ
      = D * ((Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X) * (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ) * Dᵀ := by
        rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc D]
    _ = D * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ) * Dᵀ := by rw [hE]

/-- **The corank-Gram monomialization (cert §0 load-bearing identity).** On the `b×b`-minor chart
`Q_b = D·[I_b | X]`, `det(Q_b Q_bᵀ) = (det D)² · det(I_b + X Xᵀ)` — the rank-drop singularity is the
`(det D)²` monomial; `det(I + X Xᵀ)` is a `D`-independent unit `≥ 1`. -/
theorem det_chartGram {b d : ℕ} (D : Matrix (Fin b) (Fin b) ℝ) (X : Matrix (Fin b) (Fin d) ℝ) :
    ((D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X) * (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)ᵀ).det
      = (D.det) ^ 2 * (1 + X * Xᵀ).det := by
  rw [chartGram_congr, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring

/-! ## The transverse-Schur push-through (Woodbury) -/

/-- **The push-through identity** `(I_d + Xᵀ X)⁻¹ = I_b − Xᵀ (I_b + X Xᵀ)⁻¹ X` (Woodbury at
`A = 1, U = Xᵀ, C = 1, V = X`). The algebraic heart of the transverse-Schur monomialization: it converts
the `b×b` Schur residual `I − Xᵀ (I + X Xᵀ)⁻¹ X` into the `d×d` inverse Gram `(I + Xᵀ X)⁻¹`. Needs
`I + X Xᵀ` invertible (holds on the full-rank chart: `I + X Xᵀ ≻ 0`). -/
theorem pushThrough {b d : ℕ} (X : Matrix (Fin b) (Fin d) ℝ)
    (h : IsUnit ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)) :
    ((1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X)⁻¹
      = 1 - Xᵀ * ((1 : Matrix (Fin b) (Fin b) ℝ) + X * Xᵀ)⁻¹ * X := by
  have hAC : IsUnit ((1 : Matrix (Fin b) (Fin b) ℝ)⁻¹
      + X * (1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ * Xᵀ) := by simpa using h
  have key := Matrix.add_mul_mul_inv_eq_sub (1 : Matrix (Fin d) (Fin d) ℝ) Xᵀ 1 X
    isUnit_one isUnit_one hAC
  simpa using key

/-! ## The chart null direction `N = [−X ; I_d]` — the transverse Schur monomialized by `W` -/

/-- The chart null direction `N = [−X ; I_d]` (`n×d`) annihilates `Q_b = D·[I_b | X]`: `Q_b · N = 0`
(so `col N = ker Q_b = (row Q_b)^⊥`, the transverse subspace `I − Π_b` projects onto). -/
theorem chartNull_Qb {b d : ℕ} (D : Matrix (Fin b) (Fin b) ℝ) (X : Matrix (Fin b) (Fin d) ℝ) :
    (D * Matrix.fromCols (1 : Matrix (Fin b) (Fin b) ℝ) X)
        * Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  rw [Matrix.mul_assoc, Matrix.fromCols_mul_fromRows]
  simp

/-- The pivot rows map the null direction to `W`: `Q_p · N = W` for `Q_p = [U | U X + W]`. This is the
transverse-Schur monomialization — the transverse energy of `Q_p` is carried entirely by `W`. -/
theorem chartNull_Qp {u b d : ℕ} (U : Matrix (Fin u) (Fin b) ℝ) (W : Matrix (Fin u) (Fin d) ℝ)
    (X : Matrix (Fin b) (Fin d) ℝ) :
    Matrix.fromCols U (U * X + W) * Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ) = W := by
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_neg, neg_add_cancel_left]

/-- The null-direction Gram `Nᵀ N = I_d + Xᵀ X` — the `d×d` inverse Gram that monomializes the transverse
Schur: `Q_p (I − Π_b) Q_pᵀ = W (Nᵀ N)⁻¹ Wᵀ = W (I + Xᵀ X)⁻¹ Wᵀ`. -/
theorem chartNull_gram {b d : ℕ} (X : Matrix (Fin b) (Fin d) ℝ) :
    (Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ
        * Matrix.fromRows (-X) (1 : Matrix (Fin d) (Fin d) ℝ)
      = (1 : Matrix (Fin d) (Fin d) ℝ) + Xᵀ * X := by
  rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.one_mul]
  abel

end DLNFibre.DLN.RLCT
