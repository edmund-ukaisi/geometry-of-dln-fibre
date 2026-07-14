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

end DLNFibre.DLN.RLCT
