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
- `Matrix.rank_diagonal_indicator_lt` — `rank (diagonal (fun i ↦ if i < r then 1 else 0)) = r`.
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

end DLNFibre.Core

/-- Non-vacuity witness: the `3×3` normal form `diag(1,1,0)` has rank `2` over `ℚ`. -/
example : (Matrix.diagonal (fun i : Fin 3 ↦ if (i : ℕ) < 2 then (1 : ℚ) else 0)).rank = 2 :=
  DLNFibre.Core.rank_diagonal_indicator_lt (by norm_num)
