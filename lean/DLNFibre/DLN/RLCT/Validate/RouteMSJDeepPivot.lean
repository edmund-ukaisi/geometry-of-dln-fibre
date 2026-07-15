/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.DLN.RLCT.Validate.D1JointDiffRankExact
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepAtlas

set_option linter.style.longLine false

/-!
# `RouteMSJDeepPivot` — the general-pivot CUR skeleton (deep atlas, Tide B bridge)

**Thread `genm-deepatlas`, aoyagi-full Stage 2 (branch β, NATIVE).** The load-bearing bridge that lifts
the tide-A **top-left** product-layer reduction (`deepReduce_rank`) to a **general pivot** `(ρ, κ)`, so
the telescoping resolution can read the actual-rank pivot at each recursion level (the "pivot-reindexing"
cost, done here via a rank factorization — NOT permutation bookkeeping).

## The CUR / skeleton decomposition

For `M` of rank `r` with an invertible `r×r` pivot minor `M[ρ,κ]`, the classical skeleton/CUR
decomposition holds:

    M  =  C · U⁻¹ · R,     C := M[:,κ] (pivot columns),  U := M[ρ,κ] (pivot minor),  R := M[ρ,:] (pivot rows).

Proof (Route B, via a rank factorization `M = P·Q`, `P` full column rank, `Q` full row rank): the pivot
minor `U = P[ρ,:]·Q[:,κ]` is a unit, so both square factors `P[ρ,:]`, `Q[:,κ]` are units (over ℝ,
`det` multiplies), and `C·U⁻¹·R = P·Q[:,κ]·(P[ρ,:]·Q[:,κ])⁻¹·P[ρ,:]·Q = P·Q = M` by cancellation.

## What lands here (sorry-free)

* **`generalPivot_CUR`** — `M = M.submatrix id κ * (M.submatrix ρ κ)⁻¹ * M.submatrix ρ id`, for a
  general size-`M.rank` pivot `(ρ, κ)` with `IsUnit (M.submatrix ρ κ)`. Reuses the banked rank
  factorization `exists_rank_factorization_gen`.

Network-free matrix rank over ℝ. Standalone (NOT aggregator-wired). Axiom target
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped Matrix

namespace DeepAtlas

variable {m n : ℕ}

/-- **The general-pivot CUR / skeleton decomposition.** For `M` with an invertible size-`M.rank`
pivot minor `M[ρ,κ]`, `M = (pivot columns) · (pivot minor)⁻¹ · (pivot rows)`. Via the banked rank
factorization `M = P·Q`: the pivot minor `= P[ρ]·Q[κ]` is a unit ⟹ both factors are units, and the
inverses cancel. This lifts the tide-A top-left reduction to an arbitrary pivot. -/
theorem generalPivot_CUR (M : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin M.rank ↪ Fin m) (κ : Fin M.rank ↪ Fin n)
    (hU : IsUnit (M.submatrix ρ κ)) :
    M = M.submatrix id κ * (M.submatrix ρ κ)⁻¹ * M.submatrix ρ id := by
  obtain ⟨P, Q, hM, hPr, hQr⟩ := exists_rank_factorization_gen M
  -- `M.rank` is in the `Fin M.rank` types of `ρ, κ, P, Q`, so `rw [hM]` / `subst` break; push `hM`
  -- under `.submatrix` with `congrArg` instead (the codomain type is fixed, no motive obstruction).
  have hUeq : M.submatrix ρ κ = P.submatrix ρ id * Q.submatrix id κ := by
    rw [congrArg (fun X : Matrix (Fin m) (Fin n) ℝ =>
          X.submatrix (ρ : Fin M.rank → Fin m) (κ : Fin M.rank → Fin n)) hM,
      ← submatrix_mul_equiv P Q (ρ : Fin M.rank → Fin m) (Equiv.refl (Fin M.rank))
        (κ : Fin M.rank → Fin n)]
    simp only [Equiv.coe_refl]
  have hCeq : M.submatrix id κ = P * Q.submatrix id κ := by
    rw [congrArg (fun X : Matrix (Fin m) (Fin n) ℝ =>
          X.submatrix (id : Fin m → Fin m) (κ : Fin M.rank → Fin n)) hM,
      ← submatrix_mul_equiv P Q (id : Fin m → Fin m) (Equiv.refl (Fin M.rank))
        (κ : Fin M.rank → Fin n)]
    simp only [Equiv.coe_refl, Matrix.submatrix_id_id]
  have hReq : M.submatrix ρ id = P.submatrix ρ id * Q := by
    rw [congrArg (fun X : Matrix (Fin m) (Fin n) ℝ =>
          X.submatrix (ρ : Fin M.rank → Fin m) (id : Fin n → Fin n)) hM,
      ← submatrix_mul_equiv P Q (ρ : Fin M.rank → Fin m) (Equiv.refl (Fin M.rank))
        (id : Fin n → Fin n)]
    simp only [Equiv.coe_refl, Matrix.submatrix_id_id]
  set Pρ := P.submatrix ρ id with hPρdef
  set Qκ := Q.submatrix id κ with hQκdef
  -- The pivot minor `= Pρ * Qκ` is a unit ⟹ both square factors are units (over ℝ, via `det`).
  rw [hUeq] at hU
  have hdet : Pρ.det * Qκ.det ≠ 0 := by
    have := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hU)
    rwa [Matrix.det_mul] at this
  have hPρdet : IsUnit Pρ.det := isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hdet).1
  have hQκdet : IsUnit Qκ.det := isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hdet).2
  -- Assemble: substitute the submatrices, cancel the inverses to `P*Q`, then close with `M = P*Q`.
  rw [hCeq, hUeq, hReq]
  have hprod : P * Qκ * (Pρ * Qκ)⁻¹ * (Pρ * Q) = P * Q :=
    calc P * Qκ * (Pρ * Qκ)⁻¹ * (Pρ * Q)
        = P * Qκ * (Qκ⁻¹ * Pρ⁻¹) * (Pρ * Q) := by rw [Matrix.mul_inv_rev]
      _ = P * (Qκ * (Qκ⁻¹ * Pρ⁻¹)) * (Pρ * Q) := by rw [Matrix.mul_assoc P Qκ (Qκ⁻¹ * Pρ⁻¹)]
      _ = P * Pρ⁻¹ * (Pρ * Q) := by rw [Matrix.mul_nonsing_inv_cancel_left Qκ Pρ⁻¹ hQκdet]
      _ = P * (Pρ⁻¹ * (Pρ * Q)) := by rw [Matrix.mul_assoc P Pρ⁻¹ (Pρ * Q)]
      _ = P * Q := by rw [Matrix.nonsing_inv_mul_cancel_left Pρ Q hPρdet]
  rw [hprod]; exact hM

/-- **The general-pivot rank reduction.** For any preceding head `X` and a general size-`M.rank` pivot
`(ρ, κ)` of `M`, the composed rank through `M` equals the composed rank through the reduced
`r`-column factor `C · U⁻¹ = (pivot columns) · (pivot minor)⁻¹`:

    rank(X · M)  =  rank(X · M[:,κ] · M[ρ,κ]⁻¹).

Both `≤` directions are a single `rank_mul_le_left`: `X·M = (X·C·U⁻¹)·R` (CUR) gives `≤`, and
`C = M · Sκ` (a column selection, `mul_submatrix_one`) gives `X·C·U⁻¹ = (X·M)·(Sκ·U⁻¹)` hence `≥`. This
is the general-pivot form of the tide-A `deepReduce_rank`, the composite-rank recursion step for an
arbitrary pivot at each telescoping level. -/
theorem generalPivot_reduce_rank {p : ℕ} (X : Matrix (Fin p) (Fin m) ℝ)
    (M : Matrix (Fin m) (Fin n) ℝ) (ρ : Fin M.rank ↪ Fin m) (κ : Fin M.rank ↪ Fin n)
    (hU : IsUnit (M.submatrix ρ κ)) :
    (X * M).rank = (X * M.submatrix id κ * (M.submatrix ρ κ)⁻¹).rank := by
  have hCUR := generalPivot_CUR M ρ κ hU
  -- `C = M · Sκ` where `Sκ = (1).submatrix refl κ` is the column selection.
  have hSκ : M.submatrix id κ
      = M * ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix (Equiv.refl (Fin n)) (κ : Fin M.rank → Fin n)) := by
    rw [mul_submatrix_one]
    simp only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp]
  refine le_antisymm ?_ ?_
  · -- `X·M = (X·C·U⁻¹)·R`, so `rank(X·M) ≤ rank(X·C·U⁻¹)`.
    have hXM : X * M
        = X * M.submatrix id κ * (M.submatrix ρ κ)⁻¹ * M.submatrix ρ id := by
      rw [congrArg (fun Y : Matrix (Fin m) (Fin n) ℝ => X * Y) hCUR,
        ← Matrix.mul_assoc X (M.submatrix id κ * (M.submatrix ρ κ)⁻¹) (M.submatrix ρ id),
        ← Matrix.mul_assoc X (M.submatrix id κ) (M.submatrix ρ κ)⁻¹]
    rw [hXM]
    exact Matrix.rank_mul_le_left _ _
  · -- `X·C·U⁻¹ = (X·M)·(Sκ·U⁻¹)`, so `rank(X·C·U⁻¹) ≤ rank(X·M)`.
    have hXC : X * M.submatrix id κ * (M.submatrix ρ κ)⁻¹
        = X * M * (((1 : Matrix (Fin n) (Fin n) ℝ).submatrix (Equiv.refl (Fin n))
            (κ : Fin M.rank → Fin n)) * (M.submatrix ρ κ)⁻¹) := by
      rw [hSκ, ← Matrix.mul_assoc X M
            ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix (Equiv.refl (Fin n)) (κ : Fin M.rank → Fin n)),
        Matrix.mul_assoc (X * M)
          ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix (Equiv.refl (Fin n)) (κ : Fin M.rank → Fin n))
          (M.submatrix ρ κ)⁻¹]
    rw [hXC]
    exact Matrix.rank_mul_le_left _ _

/-- Non-vacuity: both the CUR skeleton and the rank reduction apply at a concrete `3×4` effective
layer with an arbitrary size-`M.rank` unit pivot and a `2×3` preceding head. -/
example (M : Matrix (Fin 3) (Fin 4) ℝ) (ρ : Fin M.rank ↪ Fin 3) (κ : Fin M.rank ↪ Fin 4)
    (hU : IsUnit (M.submatrix ρ κ)) (X : Matrix (Fin 2) (Fin 3) ℝ) : True := by
  have _hcur := generalPivot_CUR M ρ κ hU
  have _hred := generalPivot_reduce_rank X M ρ κ hU
  trivial

end DeepAtlas

end DLNFibre.DLN.RLCT
