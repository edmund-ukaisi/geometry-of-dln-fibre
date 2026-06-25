/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# `DLNFibre.Core.RankNormalFormDim` — rank of the rank-normal-form diagonal

A small reusable fact for the chart-trivialization route to `hSweep` (thread 31): the rank-`r`
normal form `diag(1,…,1,0,…,0)` (first `r` diagonal entries `1`, rest `0`) over a field has rank
exactly `r`. Via Mathlib's `Matrix.rank_diagonal` (rank of a diagonal matrix = number of nonzero
entries) and the count `#{i : Fin n | i < r} = r`.

## Main results
- `rank_diagonal_indicator_lt` — `rank (diagonal (fun i ↦ if i < r then 1 else 0)) = r`.
- `Matrix.rank_eq_zero_iff` — over a field, `M.rank = 0 ↔ M = 0`.
-/

namespace DLNFibre.Core

open Matrix

/-- **Rank of the rank-`r` normal-form diagonal.** Over a field, the diagonal matrix on `Fin n`
whose first `r` entries are `1` and the rest `0` has rank exactly `r` (for `r ≤ n`). The matrix
heart's target shape `diag(I_r, 0)`. -/
theorem rank_diagonal_indicator_lt {K : Type*} [Field K] [DecidableEq K] {n r : ℕ} (hr : r ≤ n) :
    (Matrix.diagonal (fun i : Fin n ↦ if (i : ℕ) < r then (1 : K) else 0)).rank = r := by
  rw [Matrix.rank_diagonal]
  have hcond : ∀ i : Fin n, ((if (i : ℕ) < r then (1 : K) else 0) ≠ 0) ↔ (i : ℕ) < r := by
    intro i; constructor
    · intro h; by_contra hc; rw [if_neg hc] at h; exact h rfl
    · intro h; rw [if_pos h]; exact one_ne_zero
  have he : {i : Fin n // (if (i : ℕ) < r then (1 : K) else 0) ≠ 0} ≃ Fin r :=
    { toFun := fun i ↦ ⟨i.1.1, (hcond i.1).mp i.2⟩
      invFun := fun j ↦ ⟨⟨j.1, lt_of_lt_of_le j.2 hr⟩, (hcond _).mpr j.2⟩
      left_inv := fun i ↦ by ext; rfl
      right_inv := fun j ↦ by ext; rfl }
  rw [Fintype.card_congr he, Fintype.card_fin]

/-- **A matrix over a field has rank `0` iff it is the zero matrix.** `rank` is `finrank` of the
range of `mulVecLin`; that range is `⊥` iff `mulVecLin` is `0` iff the matrix vanishes on each
standard basis vector. -/
theorem _root_.Matrix.rank_eq_zero_iff {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) K) :
    M.rank = 0 ↔ M = 0 := by
  constructor
  · intro h
    have hr : LinearMap.range M.mulVecLin = ⊥ := by
      rw [← Submodule.finrank_eq_zero (R := K)]; exact h
    rw [LinearMap.range_eq_bot] at hr
    ext i j
    have := congrFun (congrArg (fun f ↦ f (Pi.single j 1)) hr) i
    simpa [Matrix.mulVecLin, Matrix.mulVec_single] using this
  · rintro rfl; simp [Matrix.rank]

end DLNFibre.Core

/-- Non-vacuity witness: the `3×3` normal form `diag(1,1,0)` has rank `2` over `ℚ`. -/
example : (Matrix.diagonal (fun i : Fin 3 ↦ if (i : ℕ) < 2 then (1 : ℚ) else 0)).rank = 2 :=
  DLNFibre.Core.rank_diagonal_indicator_lt (by norm_num)
