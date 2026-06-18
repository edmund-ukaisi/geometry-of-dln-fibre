import DLNFibre.Core.CThetaQIP

/-!
# `DLNFibre.Core.CThetaExplicit` — two ℤ-algebra bridges toward the explicit `(C, θ)` formula

Lehalleur–Rimányi 2024 Theorem 7.10 gives a closed form for the combinatorial codimension `C` (and
the component count `θ`) of the zero-product locus. The route from the quadratic integer program
(`Core.CThetaQIP`'s `Gqip`) to that closed form rests on two **standalone ℤ-algebra facts**, proved
here independently of the rest of the ladder (no drop-to-`m` reduction, no value assembly):

1. **Square completion** (`two_Gqipℤ_sub_sq`). With `s i := (d 0 : ℤ) − d i.succ`,

   $$ 2\,G_d(e) - \Bigl(\textstyle\sum_i e_i\Bigr)^2
        = \sum_i (e_i - s_i)^2 - \sum_i s_i^2 \qquad (e : \mathrm{Fin}\,N \to \mathbb Z). $$

   This is the algebra that turns minimising `Gqip` on the feasible face `∑ e = d 0` into minimising
   the integer distance `‖e − s‖²`. **Name = content:** in the Lean indexing of `Gqip` the shift is
   `s i = d 0 − d i.succ` (the paper's `d'_i`, `i = 1..N`, is `d i.succ` here), *not* the
   `d'_0 − d'_i` of the chart — adjusted to the true `Gqip`.

2. **Integer-square optimality** (`isLeast_sumSq`). For `m : ℕ`, `δ : ℤ` with `|δ| ≤ m`,

   $$ \min\Bigl\{ \textstyle\sum_i t_i^2 : t : \mathrm{Fin}\,m \to \mathbb Z,\ \sum_i t_i = \delta
        \Bigr\} = |\delta|, $$

   attained. The lower bound `∑ t² ≥ |δ|` holds for every `t` with `∑ t = δ` (from `|t| ≤ t²` over
   `ℤ` and the triangle inequality, no `|δ| ≤ m` needed); attainment uses `|δ| ≤ m` via an explicit
   `0`/`sgn δ`-valued witness with exactly `|δ|` nonzero coordinates. This replaces the
   Conway–Sloane closest-vector black box.

Both are pure integer algebra; neither touches the Voigt hypothesis. **Dependency rule:** `Core`
only.
-/

namespace DLNFibre.Core

open Finset

variable {N : ℕ}

/-! ## 1. The square-completion bridge -/

/-- The square-completion shift `s i := (d 0 : ℤ) − d i.succ` for `Gqip` (the paper's `d'_0 − d'_i`,
in the Lean `Gqip` indexing where `d'_i = d i.succ`). -/
def qipShift (d : Fin (N + 1) → ℕ) (i : Fin N) : ℤ := (d 0 : ℤ) - (d i.succ : ℤ)

/-- The integer form of `Gqip` (cast the ℕ data), as a function of an integer-valued `e`. Equals
`(Gqip d e : ℤ)` when `e` is a cast ℕ-vector (`Gqipℤ_eq_Gqip`). -/
def Gqipℤ (d : Fin (N + 1) → ℕ) (e : Fin N → ℤ) : ℤ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if j ≤ i then e i * (e j + (d j.succ : ℤ) - (d j.castSucc : ℤ)) else 0

/-- `Gqipℤ` on a cast ℕ-vector is the cast of `Gqip`. -/
theorem Gqipℤ_eq_Gqip (d : Fin (N + 1) → ℕ) (e : Fin N → ℕ) :
    Gqipℤ d (fun i ↦ (e i : ℤ)) = (Gqip d e : ℤ) := by
  unfold Gqipℤ Gqip
  push_cast
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ ?_))
  split_ifs
  · ring
  · rfl

/-- **The `ee` cross-term.** `2 ∑_{j ≤ i} e_i e_j − (∑ e)² = ∑ e_i²`: the over-the-triangle product,
doubled and corrected by the full square, leaves the diagonal. -/
theorem two_tri_ee_sub_sq (e : Fin N → ℤ) :
    2 * (∑ i : Fin N, ∑ j : Fin N, if j ≤ i then e i * e j else 0) - (∑ i, e i) ^ 2
      = ∑ i, (e i) ^ 2 := by
  have hsq : (∑ i, e i) ^ 2 = ∑ i : Fin N, ∑ j : Fin N, e i * e j := by
    rw [sq, Finset.sum_mul_sum Finset.univ Finset.univ e e]
  rw [hsq]
  -- `2 ∑_{j≤i} − ∑_{i,j} = ∑_{j≤i} − ∑_{j>i}`; symmetry collapses to the diagonal `∑ e_i²`.
  have hsplit : (∑ i : Fin N, ∑ j : Fin N, e i * e j)
      = (∑ i : Fin N, ∑ j : Fin N, if j ≤ i then e i * e j else 0)
        + ∑ i : Fin N, ∑ j : Fin N, if i < j then e i * e j else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases h : j ≤ i
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  -- swap `i < j` half into a `j ≤ i` half via `sum_comm`; combine with the diagonal.
  have hswap : (∑ i : Fin N, ∑ j : Fin N, if i < j then e i * e j else 0)
      = ∑ i : Fin N, ∑ j : Fin N, if j < i then e i * e j else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ ?_))
    rw [mul_comm]
  rw [hsplit, hswap]
  have hdiag : (∑ i : Fin N, ∑ j : Fin N, if j ≤ i then e i * e j else 0)
      - (∑ i : Fin N, ∑ j : Fin N, if j < i then e i * e j else 0)
      = ∑ i, (e i) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin N)), j ≠ i →
        (if j ≤ i then e i * e j else 0) - (if j < i then e i * e j else 0) = 0 := by
      intro j _ hj
      rcases lt_or_ge j i with h | h
      · rw [if_pos (le_of_lt h), if_pos h, sub_self]
      · have hij : i < j := lt_of_le_of_ne h (Ne.symm hj)
        rw [if_neg (not_le.mpr hij), if_neg (not_lt.mpr (le_of_lt hij)), sub_zero]
    rw [← Finset.sum_sub_distrib,
      Finset.sum_eq_single i hterm (fun h ↦ absurd (Finset.mem_univ i) h),
      if_pos le_rfl, if_neg (lt_irrefl i), sub_zero, sq]
  linarith [hdiag]

/-- **Telescoping shift.** `∑_{j ≤ i} (d_{j+1} − d_j) = d_{i+1} − d_0 = −(s i)`. -/
theorem sum_tri_diff (d : Fin (N + 1) → ℕ) (i : Fin N) :
    (∑ j : Fin N, if j ≤ i then (d j.succ : ℤ) - (d j.castSucc : ℤ) else 0)
      = (d i.succ : ℤ) - (d 0 : ℤ) := by
  -- reindex to `range N`, restrict to `range (i+1)`, telescope.
  have hcast : ∀ j : Fin N, ((d j.succ : ℤ) - (d j.castSucc : ℤ))
      = (fun k : ℕ ↦ (d ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : ℤ)) (j + 1)
        - (fun k : ℕ ↦ (d ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : ℤ)) j := by
    intro j
    have hj1 : (j : ℕ) + 1 ≤ N := j.isLt
    have hj0 : (j : ℕ) ≤ N := le_of_lt j.isLt
    simp only [Nat.min_eq_left hj1, Nat.min_eq_left hj0]
    rw [show (⟨(j : ℕ) + 1, by omega⟩ : Fin (N + 1)) = j.succ from Fin.ext (by simp [Fin.val_succ]),
      show (⟨(j : ℕ), by omega⟩ : Fin (N + 1)) = j.castSucc from Fin.ext (by simp)]
  set f : ℕ → ℤ := fun k ↦ (d ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : ℤ) with hf
  have hsummand : ∀ j : Fin N, (if j ≤ i then (d j.succ : ℤ) - (d j.castSucc : ℤ) else 0)
      = (if (j : ℕ) ≤ (i : ℕ) then f ((j : ℕ) + 1) - f (j : ℕ) else 0) := by
    intro j; rw [hcast j]
    exact if_congr (by rw [Fin.le_def]) rfl rfl
  rw [Finset.sum_congr rfl (fun j _ ↦ hsummand j)]
  rw [show (∑ j : Fin N, if (j : ℕ) ≤ (i : ℕ) then f ((j : ℕ) + 1) - f (j : ℕ) else 0)
      = ∑ k ∈ Finset.range N, if k ≤ (i : ℕ) then f (k + 1) - f k else 0 from
    Fin.sum_univ_eq_sum_range (fun k ↦ if k ≤ (i : ℕ) then f (k + 1) - f k else 0) N]
  have hfilter : (Finset.range N).filter (fun k ↦ k ≤ (i : ℕ)) = Finset.range ((i : ℕ) + 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]
    have := i.isLt; omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfilter, Finset.sum_range_sub f]
  have hfi1 : f ((i : ℕ) + 1) = (d i.succ : ℤ) := by
    simp only [hf, Nat.min_eq_left (i.isLt : (i : ℕ) + 1 ≤ N)]
    rw [show (⟨(i : ℕ) + 1, by omega⟩ : Fin (N + 1)) = i.succ from Fin.ext (by simp [Fin.val_succ])]
  have hf0 : f 0 = (d 0 : ℤ) := by simp [hf]
  rw [hfi1, hf0]

/-- **Square completion for `Gqip`.** With `s = qipShift d`, the ℤ-identity
`2 G_d(e) − (∑ e)² = ∑ (e_i − s_i)² − ∑ s_i²` for every integer-valued `e`. Minimising `Gqip` on the
feasible face `∑ e = d 0` is thus minimising `∑ (e_i − s_i)²`. -/
theorem two_Gqipℤ_sub_sq (d : Fin (N + 1) → ℕ) (e : Fin N → ℤ) :
    2 * Gqipℤ d e - (∑ i, e i) ^ 2
      = (∑ i, (e i - qipShift d i) ^ 2) - ∑ i, (qipShift d i) ^ 2 := by
  -- Split `Gqipℤ` into the `ee` triangle and the `eΔ` part (`Δ_j = d_{j+1} − d_j`).
  have hGsplit : Gqipℤ d e
      = (∑ i : Fin N, ∑ j : Fin N, if j ≤ i then e i * e j else 0)
        + ∑ i : Fin N, e i * ∑ j : Fin N,
            if j ≤ i then (d j.succ : ℤ) - (d j.castSucc : ℤ) else 0 := by
    unfold Gqipℤ
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases h : j ≤ i
    · rw [if_pos h, if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, if_neg h, mul_zero, add_zero]
  -- The `eΔ` part telescopes: `∑_i e_i (d_{i+1} − d_0) = −∑_i e_i s_i`.
  have heΔ : (∑ i : Fin N, e i * ∑ j : Fin N,
        if j ≤ i then (d j.succ : ℤ) - (d j.castSucc : ℤ) else 0)
      = ∑ i, e i * ((d i.succ : ℤ) - (d 0 : ℤ)) := by
    refine Finset.sum_congr rfl (fun i _ ↦ ?_); rw [sum_tri_diff]
  -- RHS expands to `∑ e_i² − 2 ∑ e_i s_i`.
  have hRHS : (∑ i, (e i - qipShift d i) ^ 2) - ∑ i, (qipShift d i) ^ 2
      = (∑ i, (e i) ^ 2) - 2 * ∑ i, e i * qipShift d i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_); ring
  rw [hGsplit, heΔ, hRHS]
  -- `2 ∑_{j≤i} e_i e_j − (∑e)² = ∑ e_i²`; the linear parts match (`s_i = d_0 − d_{i+1}`).
  have htri := two_tri_ee_sub_sq e
  have hlin : (∑ i, e i * ((d i.succ : ℤ) - (d 0 : ℤ))) + ∑ i, e i * qipShift d i = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i _ ↦ ?_); unfold qipShift; ring
  rw [mul_add]
  linarith [htri, hlin]

/-! ## 2. The integer-square optimality lemma -/

/-- The attainable sum-of-squares values `∑ t_i²` for integer `t : Fin m → ℤ` with `∑ t_i = δ`. -/
def sumSqValues (m : ℕ) (δ : ℤ) : Set ℤ :=
  { v : ℤ | ∃ t : Fin m → ℤ, (∑ i, t i) = δ ∧ (∑ i, (t i) ^ 2) = v }

/-- **Lower bound.** Any feasible `t` (`∑ t = δ`) has `∑ t² ≥ |δ|`, via `|t_i| ≤ t_i²` and the
triangle inequality. No bound on `|δ|` is needed here. -/
theorem abs_le_sumSq {m : ℕ} {δ : ℤ} {t : Fin m → ℤ} (ht : (∑ i, t i) = δ) :
    |δ| ≤ ∑ i, (t i) ^ 2 := by
  -- `|t_i| ≤ t_i²` for integers (`|a| = natAbs a ≤ a²`).
  have habs : ∀ a : ℤ, |a| ≤ a ^ 2 := fun a ↦ by
    rw [Int.abs_eq_natAbs]; exact Int.natAbs_le_self_sq a
  calc |δ| = |∑ i, t i| := by rw [ht]
    _ ≤ ∑ i, |t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (t i) ^ 2 := Finset.sum_le_sum (fun i _ ↦ habs (t i))

/-- **The integer-square optimum.** For `|δ| ≤ m`, `|δ|` is the least attainable `∑ t²` subject to
`∑ t = δ` — the lower bound `abs_le_sumSq` plus an explicit `0`/`sgn δ`-valued attaining witness. -/
theorem isLeast_sumSq (m : ℕ) (δ : ℤ) (hδ : |δ| ≤ m) :
    IsLeast (sumSqValues m δ) |δ| := by
  have hnat : δ.natAbs ≤ m := by rw [Int.abs_eq_natAbs] at hδ; exact_mod_cast hδ
  -- Generic count: `∑_{i : Fin m} (if (i:ℕ) < δ.natAbs then c else 0) = δ.natAbs • c` (needs
  -- `δ.natAbs ≤ m`).
  have hcount : ∀ c : ℤ,
      (∑ i : Fin m, if (i : ℕ) < δ.natAbs then c else 0) = δ.natAbs • c := by
    intro c
    rw [show (∑ i : Fin m, if (i : ℕ) < δ.natAbs then c else 0)
        = ∑ k ∈ Finset.range m, if k < δ.natAbs then c else 0 from
      Fin.sum_univ_eq_sum_range (fun k ↦ if k < δ.natAbs then c else 0) m]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    have hfilter : (Finset.range m).filter (fun k ↦ k < δ.natAbs) = Finset.range δ.natAbs := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilter, Finset.card_range]
  -- The explicit `0`/`sgn δ`-valued witness: `δ.natAbs` coords equal `δ.sign`, the rest `0`.
  set t : Fin m → ℤ := fun i ↦ if (i : ℕ) < δ.natAbs then δ.sign else 0 with ht
  -- `∑ t = δ`: `δ.natAbs · δ.sign = δ`.
  have hsum : (∑ i, t i) = δ := by
    simp only [ht]
    rw [hcount δ.sign, nsmul_eq_mul, mul_comm, Int.sign_mul_natAbs]
  -- `∑ t² = |δ|`: `δ.natAbs · δ.sign² = δ.natAbs = |δ|`.
  have hsumsq : (∑ i, (t i) ^ 2) = |δ| := by
    have hsq : ∀ i, (t i) ^ 2 = if (i : ℕ) < δ.natAbs then δ.sign ^ 2 else 0 := by
      intro i; simp only [ht]; split_ifs with h
      · rfl
      · rw [zero_pow two_ne_zero]
    rw [Finset.sum_congr rfl (fun i _ ↦ hsq i), hcount (δ.sign ^ 2), nsmul_eq_mul,
      Int.abs_eq_natAbs]
    -- `δ.natAbs · δ.sign² = δ.sign · (δ.sign · δ.natAbs) = δ.sign · δ = δ.natAbs`.
    have hsignAbs : δ.sign * (δ.natAbs : ℤ) = δ := Int.sign_mul_natAbs δ
    calc (δ.natAbs : ℤ) * δ.sign ^ 2
        = δ.sign * (δ.sign * (δ.natAbs : ℤ)) := by ring
      _ = δ.sign * δ := by rw [hsignAbs]
      _ = (δ.natAbs : ℤ) := (Int.sign_mul_self_eq_natAbs δ)
  refine ⟨⟨t, hsum, hsumsq⟩, ?_⟩
  -- Lower bound: every attainable value is `≥ |δ|`.
  rintro v ⟨s, hs, rfl⟩
  exact abs_le_sumSq hs

/-! ## Witnesses (non-vacuity)

The two bridges fire at concrete data. For square completion, `d = (2,2,2)` and the QIP minimiser
`e = (1,1)`: `2 · G_d(1,1) − (1+1)² = 2·3 − 4 = 2`, and `s = (d_0 − d_1, d_0 − d_2) = (0,0)`, so the
RHS `∑(e_i − s_i)² − ∑ s_i² = (1+1) − 0 = 2`. For the integer-square optimum, `m = 3`, `δ = 2`:
`min ∑ t² = |δ| = 2`, with witness `t = (1,1,0)`. -/

section Witness

/-- **Square completion at `(2,2,2)`, `e = (1,1)`** — the LHS `2·G_d(1,1) − (∑e)²` evaluates to `2`,
matching the proven identity's RHS `∑(e_i − s_i)² − ∑ s_i² = 2` (here `s = (0,0)`). -/
theorem two_Gqipℤ_sub_sq_d222 :
    2 * Gqipℤ d222 ![1, 1] - (∑ i, (![1, 1] : Fin 2 → ℤ) i) ^ 2 = 2 := by decide

/-- **`m = 3`, `δ = 2`: the integer-square optimum is `|δ| = 2`** (witness `t = (1,1,0)`). -/
theorem isLeast_sumSq_3_2 : IsLeast (sumSqValues 3 2) 2 := by
  have h : (|(2 : ℤ)| : ℤ) = 2 := by decide
  have := isLeast_sumSq 3 2 (by decide)
  rwa [h] at this

end Witness

end DLNFibre.Core
