/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.RankNormalFormDim
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# `DLNFibre.Core.SchurChartIff` — the rung-1 chart-membership iff

The rung-1 capstone of the route-(c) chart-trivialization (thread 31): on the Schur chart
`{detΔ ≠ 0}`, a block matrix `M = [[Δ, B12], [B21, B22]]` over a field satisfies `rank M ≤ r`
(equivalently `rank M = r`) **iff** the Schur relation `B22 = B21 · Δ⁻¹ · B12` holds.

The proof is the assembly of the LANDED rung-1 helpers (`RankNormalFormDim`) with Mathlib's
LDU block factorization `fromBlocks_eq_of_invertible₁₁`:

1. `M = L · diag(Δ, Schur) · U` with `Schur = B22 − B21 Δ⁻¹ B12` (LDU, `L`/`U` unitriangular units).
2. `L`, `U` units ⟹ `rank M = rank (diag(Δ, Schur))` (`rank_mul_eq_*_of_isUnit_det`).
3. block-diagonal additivity (`rank_fromBlocks_zero_offdiag`) ⟹ `rank M = rank Δ + rank Schur`.
4. `Δ` invertible (`r×r`) ⟹ `rank Δ = r` (`rank_of_isUnit`).
5. `rank M = r + rank Schur`, so `rank M ≤ r ⟺ rank Schur = 0 ⟺ Schur = 0` (`rank_eq_zero_iff`)
   `⟺ B22 = B21 Δ⁻¹ B12`.

Network-free, over any field. The matrix heart for the chart normalization.

## Main results
- `rank_fromBlocks_invertible₁₁` — `rank [[Δ,B12],[B21,B22]] = r + rank (B22 − B21 Δ⁻¹ B12)`.
- `rank_le_iff_schur_eq` — `rank M ≤ r ↔ B22 = B21 Δ⁻¹ B12` (the chart-membership iff).
- `rank_eq_iff_schur_eq` — `rank M = r ↔ B22 = B21 Δ⁻¹ B12` (exact-rank form).
-/

namespace DLNFibre.Core

open Matrix

variable {K : Type*} [Field K] {r s t : ℕ}

/-- **Block-rank via the Schur complement.** For `Δ` invertible (`r×r`), the rank of the block
matrix `[[Δ, B12], [B21, B22]]` is `r + rank (B22 − B21 Δ⁻¹ B12)`: the LDU factorization conjugates
`M` to `diag(Δ, Schur)` by unitriangular units, and the block-diagonal rank adds. -/
theorem rank_fromBlocks_invertible₁₁
    (Δ : Matrix (Fin r) (Fin r) K) (B12 : Matrix (Fin r) (Fin t) K)
    (B21 : Matrix (Fin s) (Fin r) K) (B22 : Matrix (Fin s) (Fin t) K) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks Δ B12 B21 B22).rank = r + (B22 - B21 * Δ⁻¹ * B12).rank := by
  -- Promote `IsUnit Δ.det` to an `Invertible Δ` instance for the LDU lemma.
  have invΔ : Invertible Δ := Δ.invertibleOfIsUnitDet hΔ
  -- The LDU factorization `M = L · diag(Δ, Schur) · U`.
  have hLDU := Matrix.fromBlocks_eq_of_invertible₁₁ Δ B12 B21 B22
  -- The lower-unitriangular `L` and upper-unitriangular `U` are units (det 1).
  have hLdet : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 (B21 * ⅟Δ) 1).det := by
    rw [Matrix.det_fromBlocks_zero₁₂]; simp
  have hUdet : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) (⅟Δ * B12) 0 1).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]; simp
  rw [hLDU, rank_mul_eq_left_of_isUnit_det _ _ hUdet,
    rank_mul_eq_right_of_isUnit_det _ _ hLdet,
    Matrix.rank_fromBlocks_zero_offdiag, rank_of_isUnit Δ ((Matrix.isUnit_iff_isUnit_det _).mpr hΔ),
    Fintype.card_fin]
  -- `⅟Δ = Δ⁻¹` (the canonical inverse from `IsUnit`).
  congr 1
  rw [invOf_eq_nonsing_inv]

/-- **The chart-membership iff (≤ form).** On the chart `detΔ ≠ 0`, `rank [[Δ,B12],[B21,B22]] ≤ r`
iff the Schur relation `B22 = B21 Δ⁻¹ B12` holds. -/
theorem rank_le_iff_schur_eq
    (Δ : Matrix (Fin r) (Fin r) K) (B12 : Matrix (Fin r) (Fin t) K)
    (B21 : Matrix (Fin s) (Fin r) K) (B22 : Matrix (Fin s) (Fin t) K) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks Δ B12 B21 B22).rank ≤ r ↔ B22 = B21 * Δ⁻¹ * B12 := by
  rw [rank_fromBlocks_invertible₁₁ Δ B12 B21 B22 hΔ]
  constructor
  · intro h
    have hz : (B22 - B21 * Δ⁻¹ * B12).rank = 0 := by omega
    rw [Matrix.rank_eq_zero_iff] at hz
    exact sub_eq_zero.mp hz
  · intro h
    rw [h, sub_self, (Matrix.rank_eq_zero_iff (0 : Matrix (Fin s) (Fin t) K)).mpr rfl]
    omega

/-- **The chart-membership iff (= form).** On the chart `detΔ ≠ 0`, `rank [[Δ,B12],[B21,B22]] = r`
iff the Schur relation `B22 = B21 Δ⁻¹ B12` holds. (The `r` lower bound is automatic from the
invertible pivot block.) -/
theorem rank_eq_iff_schur_eq
    (Δ : Matrix (Fin r) (Fin r) K) (B12 : Matrix (Fin r) (Fin t) K)
    (B21 : Matrix (Fin s) (Fin r) K) (B22 : Matrix (Fin s) (Fin t) K) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks Δ B12 B21 B22).rank = r ↔ B22 = B21 * Δ⁻¹ * B12 := by
  rw [rank_fromBlocks_invertible₁₁ Δ B12 B21 B22 hΔ]
  constructor
  · intro h
    have hz : (B22 - B21 * Δ⁻¹ * B12).rank = 0 := by omega
    rw [Matrix.rank_eq_zero_iff] at hz
    exact sub_eq_zero.mp hz
  · intro h
    rw [h, sub_self, (Matrix.rank_eq_zero_iff (0 : Matrix (Fin s) (Fin t) K)).mpr rfl, add_zero]

end DLNFibre.Core

/-- Non-vacuity witness: `[[1,0],[0,0]]` (i.e. `Δ = [1]`, `B12 = B21 = [0]`, `B22 = [0]`) over `ℚ`
has rank `≤ 1`, and indeed satisfies the Schur relation `0 = 0`. -/
example :
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) (0 : Matrix (Fin 1) (Fin 1) ℚ)
        (0 : Matrix (Fin 1) (Fin 1) ℚ) (0 : Matrix (Fin 1) (Fin 1) ℚ)).rank ≤ 1 :=
  (DLNFibre.Core.rank_le_iff_schur_eq 1 0 0 0 (by simp)).mpr (by simp)
