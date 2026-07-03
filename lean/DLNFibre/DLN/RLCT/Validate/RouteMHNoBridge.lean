import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanMinAdm

/-!
# `RouteMHNoBridge` — the `¬InteriorDrop ⟹ NoInteriorBothDrop` bridge, ∀L

The general-`L` R1-lower achiever's clean/smeared branches carry `¬InteriorDrop`; the `minAdm`
collapse (`minAdm_eq_deepRows_mul_last`) consumes `NoInteriorBothDrop`. This module bridges the two
STANDALONE (no signature change to any existing result): for `0 < Wext M L`,

  **`¬ InteriorDrop M → NoInteriorBothDrop M`.**

## Why it is true (argmin exchange)

`InteriorDrop` needs a row-drop at some interior `p` PLUS a col-drop on the WHOLE tail `[p, L−1]`;
`¬NoInteriorBothDrop` needs only a SINGLE interior boundary `s₀` with BOTH a row- and a col-drop.
We prove the contrapositive: an interior both-drop at `s₀` forces `InteriorDrop` (witness `p = s₀`).

Write, along the achiever path, `T(k) = Text M (tach M) k` and `W(k) = Wext M k`; the per-boundary
residual blocks are `r_s = T(s) − T(s+1) ≥ 0` and `c_s = W(s) − T(s+1) ≥ 0` (`rBlock`/`cBlock` at
`j = s−1`), with `∑_s r_s c_s = minAdm M = Mval M (tStar M)` (the achiever-path argmin value).

Given a both-drop at `s₀`, suppose the tail col-drop fails at some `b ∈ [s₀, L−1]` (`c_b = 0`); take
the FIRST such `b` (strong induction), so `c_s > 0` on `[s₀, b−1]` and `b > s₀`. Let `q` be the LAST
row-drop in `[s₀, b−1]` (exists — `s₀` is one). Raise the achiever tuple by 1 on the contiguous
`tStar`-index block `[q−1, b−2]` (equivalently `T(s) += 1` for `s ∈ [q+1, b]`): the result `T'` is
admissible (per-layer bounds protected by `c_s > 0` on `[q, b−1]` and the row-drop at `q`;
weak-decrease from `r_q > 0` on top of the flat middle) and `Mval M T' = minAdm + (1 − r_q − c_q) ≤
minAdm − 1 < minAdm`, contradicting `Finset.inf'_le`.

Pure combinatorics; axiom footprint `[propext, Classical.choice, Quot.sound]` (the `tStar` argmin
choice; NO `monomial_rlct`).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators
open Finset

variable {L : ℕ}

/-! ## The block-raise tuple -/

/-- Raise the achiever tuple `tStar M` by `1` on the contiguous `tStar`-index block `[lo, hi]`. -/
noncomputable def raiseTup (M : Fin (L + 1) → ℕ) (lo hi : ℕ) : Fin L → ℕ :=
  fun j => tStar M j + (if lo ≤ j.val ∧ j.val ≤ hi then 1 else 0)

theorem raiseTup_of_mem (M : Fin (L + 1) → ℕ) {lo hi : ℕ} {j : Fin L}
    (h : lo ≤ j.val ∧ j.val ≤ hi) : raiseTup M lo hi j = tStar M j + 1 := by
  simp [raiseTup, h]

theorem raiseTup_of_not_mem (M : Fin (L + 1) → ℕ) {lo hi : ℕ} {j : Fin L}
    (h : ¬ (lo ≤ j.val ∧ j.val ≤ hi)) : raiseTup M lo hi j = tStar M j := by
  simp [raiseTup, h]

/-- The `ℤ`-valued current-bump indicator: `1` on `[q−1, b−2]`. -/
noncomputable def uCur (q b : ℕ) (j : Fin L) : ℤ :=
  if q - 1 ≤ j.val ∧ j.val ≤ b - 2 then 1 else 0

/-- The `ℤ`-valued predecessor-bump indicator: `1` on `[q, b−1]` (the support of `tPrev` change). -/
noncomputable def uPrevB (q b : ℕ) (j : Fin L) : ℤ :=
  if q ≤ j.val ∧ j.val ≤ b - 1 then 1 else 0

/-- The raised tuple's value over `ℤ`: `T' j = tStar j + uCur`. -/
theorem raiseTup_cast (M : Fin (L + 1) → ℕ) (q b : ℕ) (j : Fin L) :
    ((raiseTup M (q - 1) (b - 2) j : ℤ)) = (tStar M j : ℤ) + uCur q b j := by
  unfold raiseTup uCur
  by_cases h : q - 1 ≤ j.val ∧ j.val ≤ b - 2
  · rw [if_pos h, if_pos h]; push_cast; ring
  · rw [if_neg h, if_neg h]; push_cast; ring

/-- The `tPrev` of the raised tuple: `tPrev T' j = tPrev tStar j + uPrevB` (`1 ≤ q`, `2 ≤ b`). -/
theorem tPrev_raiseTup (M : Fin (L + 1) → ℕ) (q b : ℕ) (hq : 1 ≤ q) (hb : 2 ≤ b) (j : Fin L) :
    tPrev M (raiseTup M (q - 1) (b - 2)) j = tPrev M (tStar M) j + uPrevB q b j := by
  unfold tPrev uPrevB
  by_cases hj0 : j.val = 0
  · -- both `tPrev`s read `M 0`; predecessor-bump is 0 since `q ≥ 1` forces `q ≤ 0` false
    have : ¬ (q ≤ j.val ∧ j.val ≤ b - 1) := by omega
    simp only [if_pos hj0, if_neg this, add_zero]
  · simp only [if_neg hj0]
    -- `tPrev T' j = T' ⟨j-1⟩ = tStar ⟨j-1⟩ + [q-1 ≤ j-1 ≤ b-2]`; that predicate ↔ `q ≤ j ≤ b-1`
    have hcast := raiseTup_cast M q b (⟨j.val - 1, by omega⟩ : Fin L)
    rw [hcast]
    unfold uCur
    have hiff : (q - 1 ≤ (⟨j.val - 1, by omega⟩ : Fin L).val ∧
        (⟨j.val - 1, by omega⟩ : Fin L).val ≤ b - 2) ↔ (q ≤ j.val ∧ j.val ≤ b - 1) := by
      change (q - 1 ≤ j.val - 1 ∧ j.val - 1 ≤ b - 2) ↔ (q ≤ j.val ∧ j.val ≤ b - 1)
      omega
    by_cases h : q ≤ j.val ∧ j.val ≤ b - 1
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]

/-! ## The `Mval` delta of the block raise -/

/-- The `Mval`-summand along the achiever path is the block product `rBlock · cBlock`. -/
theorem Mval_summand_tStar (M : Fin (L + 1) → ℕ) (j : Fin L) :
    (tPrev M (tStar M) j - (tStar M j : ℤ)) * ((M j.succ : ℤ) - (tStar M j : ℤ))
      = rBlock M j * cBlock M j := rfl

/-- **The `Mval` delta of the block raise.** Raising `tStar M` on the block `[q−1, b−2]` changes the
codim value by exactly `1 − r_q − c_q`, provided the middle is flat (`rBlock = 0` on `[q, b−2]`) and
the top col-block vanishes (`cBlock ⟨b−1⟩ = 0`). Pure `Mval`-arithmetic (no admissibility). -/
theorem Mval_raiseTup (M : Fin (L + 1) → ℕ) (q b : ℕ)
    (hq : 1 ≤ q) (hb : 2 ≤ b) (hqb : q ≤ b - 1) (hbL : b - 1 < L)
    (hflat : ∀ j : Fin L, q ≤ j.val → j.val ≤ b - 2 → rBlock M j = 0)
    (hcb : cBlock M ⟨b - 1, hbL⟩ = 0) :
    Mval M (raiseTup M (q - 1) (b - 2))
      = Mval M (tStar M) + (1 - rBlock M ⟨q - 1, by omega⟩ - cBlock M ⟨q - 1, by omega⟩) := by
  -- work with the difference of summands `g j`
  set jStar : Fin L := ⟨q - 1, by omega⟩ with hjStar
  have hkey : Mval M (raiseTup M (q - 1) (b - 2)) - Mval M (tStar M)
      = 1 - rBlock M jStar - cBlock M jStar := by
    unfold Mval
    rw [← Finset.sum_sub_distrib]
    -- each summand `g j = f' j - f j`; collapse the sum to `j = jStar`
    have hgStar : ∀ j : Fin L,
        (tPrev M (raiseTup M (q - 1) (b - 2)) j - (raiseTup M (q - 1) (b - 2) j : ℤ))
            * ((M j.succ : ℤ) - (raiseTup M (q - 1) (b - 2) j : ℤ))
          - (tPrev M (tStar M) j - (tStar M j : ℤ)) * ((M j.succ : ℤ) - (tStar M j : ℤ))
        = (rBlock M j + uPrevB q b j - uCur q b j) * (cBlock M j - uCur q b j)
            - rBlock M j * cBlock M j := by
      intro j
      rw [tPrev_raiseTup M q b hq hb j, raiseTup_cast M q b j]
      rw [Mval_summand_tStar M j]
      -- rewrite `tPrev - tStar = rBlock` and `Msucc - tStar = cBlock`
      have hr : tPrev M (tStar M) j - (tStar M j : ℤ) = rBlock M j := rfl
      have hc : (M j.succ : ℤ) - (tStar M j : ℤ) = cBlock M j := rfl
      rw [show tPrev M (tStar M) j + uPrevB q b j - ((tStar M j : ℤ) + uCur q b j)
            = (tPrev M (tStar M) j - (tStar M j : ℤ)) + uPrevB q b j - uCur q b j from by ring,
          show (M j.succ : ℤ) - ((tStar M j : ℤ) + uCur q b j)
            = ((M j.succ : ℤ) - (tStar M j : ℤ)) - uCur q b j from by ring,
          hr, hc]
    rw [Finset.sum_congr rfl (fun j _ => hgStar j)]
    -- collapse to jStar
    rw [Finset.sum_eq_single_of_mem jStar (Finset.mem_univ _) ?_]
    · -- value at jStar: uCur = 1, uPrevB = 0
      have huc : uCur q b jStar = 1 := by
        unfold uCur; rw [if_pos]; constructor <;> (simp only [hjStar]; omega)
      have hup : uPrevB q b jStar = 0 := by
        unfold uPrevB; rw [if_neg]; rintro ⟨h1, _⟩; simp only [hjStar] at h1; omega
      rw [huc, hup]; ring
    · -- g j = 0 for j ≠ jStar
      intro j _ hjne
      -- split on the two indicators
      by_cases hu : q - 1 ≤ j.val ∧ j.val ≤ b - 2
      · -- uCur = 1
        have huc : uCur q b j = 1 := by unfold uCur; rw [if_pos hu]
        by_cases hp : q ≤ j.val ∧ j.val ≤ b - 1
        · -- interior: uPrevB = 1 too ⟹ delta = -rBlock, and rBlock = 0 by flatness
          have hup : uPrevB q b j = 1 := by unfold uPrevB; rw [if_pos hp]
          have hr0 : rBlock M j = 0 := hflat j hp.1 hu.2
          rw [huc, hup, hr0]; ring
        · -- uCur=1, uPrevB=0 ⟹ j = jStar (contradiction)
          exfalso; apply hjne
          apply Fin.ext; simp only [hjStar]
          -- ¬hp with hu forces j.val = q - 1
          have : ¬ (q ≤ j.val ∧ j.val ≤ b - 1) := hp
          omega
      · -- uCur = 0
        have huc : uCur q b j = 0 := by unfold uCur; rw [if_neg hu]
        by_cases hp : q ≤ j.val ∧ j.val ≤ b - 1
        · -- top: uCur=0, uPrevB=1 ⟹ j = ⟨b-1⟩, delta = cBlock = 0
          have hup : uPrevB q b j = 1 := by unfold uPrevB; rw [if_pos hp]
          have hjb : j = (⟨b - 1, hbL⟩ : Fin L) := by
            apply Fin.ext; simp only []; omega
          have hcb0 : cBlock M j = 0 := by rw [hjb]; exact hcb
          rw [huc, hup, hcb0]; ring
        · -- both 0 ⟹ delta = 0
          have hup : uPrevB q b j = 0 := by unfold uPrevB; rw [if_neg hp]
          rw [huc, hup]; ring
  linarith [hkey]

/-! ## Admissibility of the block raise -/

/-- **The block raise stays admissible.** With the col-drop tail (`cBlock > 0` on the raised block
`[q−1, b−2]`) protecting the per-layer bound, the row-drop at `q` (`rBlock ⟨q−1⟩ > 0`) protecting
bottom of the weak-decrease, and the block strictly below `L−1` (last-exponent stays `0`). -/
theorem raiseTup_mem_Adm (M : Fin (L + 1) → ℕ) (q b : ℕ)
    (hq : 1 ≤ q) (hqb : q ≤ b - 1) (hbL : b - 1 < L) (hL : 0 < L)
    (hrow : 0 < rBlock M ⟨q - 1, by omega⟩)
    (hcol : ∀ j : Fin L, q - 1 ≤ j.val → j.val ≤ b - 2 → 0 < cBlock M j) :
    raiseTup M (q - 1) (b - 2) ∈ Adm M := by
  obtain ⟨hstarB, hstarDec, hstarLast⟩ := (Finset.mem_filter.1 (tStar_mem M)).2
  -- the ℤ-shape of `tStar`'s admissibility bounds, via rBlock/cBlock
  rw [Adm, Finset.mem_filter]
  have hbound : ∀ j : Fin L, raiseTup M (q - 1) (b - 2) j ≤ admBound M j := by
    intro j
    by_cases hu : q - 1 ≤ j.val ∧ j.val ≤ b - 2
    · rw [raiseTup_of_mem M hu]
      -- raised: need tStar j + 1 ≤ admBound j, from cBlock > 0 (and rBlock > 0 at the corner j=0)
      have hcj : 0 < cBlock M j := hcol j hu.1 hu.2
      -- cBlock M j = M j.succ - tStar j > 0  ⟹  tStar j < M j.succ
      have hcjlt : (tStar M j : ℤ) < (M j.succ : ℤ) := by
        have : (0 : ℤ) < (M j.succ : ℤ) - (tStar M j : ℤ) := hcj
        linarith
      by_cases hj0 : j.val = 0
      · -- admBound 0 = min (M 0) (M 1); also need tStar 0 < M 0 from the row-drop
        rw [admBound, if_pos hj0]
        -- j = 0, and q = 1 (since q-1 ≤ j.val = 0 and q ≥ 1)
        have hq1 : q = 1 := by omega
        have hjeq : j = (⟨q - 1, by omega⟩ : Fin L) := by apply Fin.ext; simp only []; omega
        have hrj : 0 < rBlock M j := by rw [hjeq]; exact hrow
        -- rBlock M 0 = tPrev 0 - tStar 0 = M 0 - tStar 0 > 0 ⟹ tStar 0 < M 0
        have hr0 : rBlock M j = (M 0 : ℤ) - (tStar M j : ℤ) := by
          rw [rBlock, tPrev, if_pos hj0]
        have hrlt : (tStar M j : ℤ) < (M 0 : ℤ) := by
          rw [hr0] at hrj; linarith
        -- M j.succ = M 1 (since j.val = 0)
        have hsucc : M j.succ = M 1 := by
          congr 1; apply Fin.ext
          rw [Fin.val_succ, hj0, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
        rw [hsucc] at hcjlt
        have h1 : tStar M j < M 0 := by exact_mod_cast hrlt
        have h2 : tStar M j < M 1 := by exact_mod_cast hcjlt
        omega
      · rw [admBound, if_neg hj0]
        have : tStar M j < M j.succ := by exact_mod_cast hcjlt
        omega
    · rw [raiseTup_of_not_mem M hu]; exact hstarB j
  refine ⟨?_, hbound, ?_, ?_⟩
  · -- membership in the pi-finset (from the per-layer bound)
    rw [Fintype.mem_piFinset]; intro j; rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hbound j)
  · -- weak-decrease
    intro i j hij
    have hijN : i.val ≤ j.val := hij
    by_cases hui : q - 1 ≤ i.val ∧ i.val ≤ b - 2
    · by_cases huj : q - 1 ≤ j.val ∧ j.val ≤ b - 2
      · -- both raised
        rw [raiseTup_of_mem M hui, raiseTup_of_mem M huj]
        exact Nat.add_le_add_right (hstarDec i j hij) 1
      · -- i in, j out (so j > b-2)
        rw [raiseTup_of_mem M hui, raiseTup_of_not_mem M huj]
        exact le_trans (hstarDec i j hij) (Nat.le_succ _)
    · by_cases huj : q - 1 ≤ j.val ∧ j.val ≤ b - 2
      · -- i out, j in ⟹ i < q-1 (so q ≥ 2), use the row-drop at q
        rw [raiseTup_of_not_mem M hui, raiseTup_of_mem M huj]
        -- i.val < q - 1, and j.val ≥ q - 1
        have hilt : i.val < q - 1 := by omega
        have hq2 : 2 ≤ q := by omega
        -- the row-drop: tStar ⟨q-1⟩ < tStar ⟨q-2⟩
        have hrowlt : tStar M ⟨q - 1, by omega⟩ < tStar M ⟨q - 2, by omega⟩ := by
          have hidx : (⟨(⟨q - 1, by omega⟩ : Fin L).val - 1, by omega⟩ : Fin L)
              = (⟨q - 2, by omega⟩ : Fin L) := by apply Fin.ext; simp only []; omega
          have hr : rBlock M ⟨q - 1, by omega⟩
              = (tStar M ⟨q - 2, by omega⟩ : ℤ) - (tStar M ⟨q - 1, by omega⟩ : ℤ) := by
            rw [rBlock, tPrev, if_neg (by simp only []; omega), hidx]
          rw [hr] at hrow
          have : (tStar M ⟨q - 1, by omega⟩ : ℤ) < (tStar M ⟨q - 2, by omega⟩ : ℤ) := by linarith
          exact_mod_cast this
        -- tStar j ≤ tStar ⟨q-1⟩ (j ≥ q-1) and tStar ⟨q-2⟩ ≤ tStar i (i ≤ q-2)
        have hjle : tStar M j ≤ tStar M ⟨q - 1, by omega⟩ :=
          hstarDec ⟨q - 1, by omega⟩ j (by simp only [Fin.le_def]; omega)
        have hile : tStar M ⟨q - 2, by omega⟩ ≤ tStar M i :=
          hstarDec i ⟨q - 2, by omega⟩ (by simp only [Fin.le_def]; omega)
        omega
      · -- both out
        rw [raiseTup_of_not_mem M hui, raiseTup_of_not_mem M huj]
        exact hstarDec i j hij
  · -- last-exponent zero: L-1 ∉ [q-1, b-2]
    intro j hjlast
    have hnot : ¬ (q - 1 ≤ j.val ∧ j.val ≤ b - 2) := by omega
    rw [raiseTup_of_not_mem M hnot]
    exact hstarLast j hjlast

/-! ## Row/col-drop ↔ block bridges (Text-boundary `s` ↔ block index `⟨s−1⟩`) -/

/-- `0 < rBlock M ⟨s−1⟩ ⟺ Text(s+1) < Text(s)` (row-drop at boundary `s`); `1 ≤ s`, `s−1 < L`. -/
theorem rBlock_pos_iff (M : Fin (L + 1) → ℕ) (s : ℕ) (hs : 1 ≤ s) (hsL : s - 1 < L) :
    0 < rBlock M ⟨s - 1, hsL⟩ ↔ Text M (tach M) (s + 1) < Text M (tach M) s := by
  rw [rBlock_eq_Text]
  have e1 : (⟨s - 1, hsL⟩ : Fin L).val + 1 = s := by simp only []; omega
  have e2 : (⟨s - 1, hsL⟩ : Fin L).val + 2 = s + 1 := by simp only []; omega
  rw [e1, e2]; omega

/-- `0 < cBlock M ⟨s−1⟩ ⟺ Text(s+1) < Wext(s)` (col-drop at boundary `s`); `1 ≤ s`, `s−1 < L`. -/
theorem cBlock_pos_iff (M : Fin (L + 1) → ℕ) (s : ℕ) (hs : 1 ≤ s) (hsL : s - 1 < L) :
    0 < cBlock M ⟨s - 1, hsL⟩ ↔ Text M (tach M) (s + 1) < Wext M s := by
  rw [cBlock_eq_Wext]
  have e1 : (⟨s - 1, hsL⟩ : Fin L).val + 1 = s := by simp only []; omega
  have e2 : (⟨s - 1, hsL⟩ : Fin L).val + 2 = s + 1 := by simp only []; omega
  rw [e1, e2]; omega

/-! ## The exchange contradiction -/

/-- **The exchange contradiction.** A both-drop at interior `s₀`, together with a boundary `b ∈
(s₀, L−1]` that fails to col-drop while every boundary in `[s₀, b−1]` does, is impossible: the
plateau-raise between the last row-drop `q ∈ [s₀, b−1]` and `b` yields an admissible tuple of
smaller `Mval`, contradicting minimality of `tStar`. -/
theorem exchange_contra (M : Fin (L + 1) → ℕ) (hL : 0 < L) (s₀ b : ℕ)
    (hs₀1 : 1 ≤ s₀) (hs₀b : s₀ < b) (hbL : b ≤ L - 1)
    (hrow₀ : Text M (tach M) (s₀ + 1) < Text M (tach M) s₀)
    (hbelow : ∀ s, s₀ ≤ s → s ≤ b - 1 → Text M (tach M) (s + 1) < Wext M s)
    (hfail : ¬ (Text M (tach M) (b + 1) < Wext M b)) : False := by
  -- the filtered set of row-drops in [s₀, b-1] is nonempty (contains s₀)
  set S : Finset ℕ := (Finset.Icc s₀ (b - 1)).filter
    (fun s => Text M (tach M) (s + 1) < Text M (tach M) s) with hS
  have hs₀mem : s₀ ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨le_refl _, by omega⟩, hrow₀⟩
  have hSne : S.Nonempty := ⟨s₀, hs₀mem⟩
  set q : ℕ := S.max' hSne with hq
  have hqmem : q ∈ S := S.max'_mem hSne
  have hqIcc : q ∈ Finset.Icc s₀ (b - 1) := (Finset.mem_filter.1 hqmem).1
  have hqrow : Text M (tach M) (q + 1) < Text M (tach M) q := (Finset.mem_filter.1 hqmem).2
  have hqlo : s₀ ≤ q := (Finset.mem_Icc.1 hqIcc).1
  have hqhi : q ≤ b - 1 := (Finset.mem_Icc.1 hqIcc).2
  -- q is the LAST row-drop: no row-drop strictly above q up to b-1
  have hqmax : ∀ s, q < s → s ≤ b - 1 → ¬ (Text M (tach M) (s + 1) < Text M (tach M) s) := by
    intro s hqs hsb hrs
    have : s ∈ S := by rw [hS, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, hsb⟩, hrs⟩
    have := S.le_max' s this
    omega
  -- ranges for the block lemmas
  have hq1 : 1 ≤ q := by omega
  have hb2 : 2 ≤ b := by omega
  have hqb1 : q ≤ b - 1 := hqhi
  have hbm1L : b - 1 < L := by omega
  -- hrow : 0 < rBlock ⟨q-1⟩
  have hrowB : 0 < rBlock M ⟨q - 1, by omega⟩ :=
    (rBlock_pos_iff M q hq1 (by omega)).mpr hqrow
  -- hcol : cBlock > 0 on the block [q-1, b-2]  (Text boundaries [q, b-1] ⊆ [s₀, b-1])
  have hcolB : ∀ j : Fin L, q - 1 ≤ j.val → j.val ≤ b - 2 → 0 < cBlock M j := by
    intro j hjlo hjhi
    have hsj : (⟨(j.val + 1) - 1, by omega⟩ : Fin L) = j := by apply Fin.ext; simp only []; omega
    have : 0 < cBlock M ⟨(j.val + 1) - 1, by omega⟩ := by
      rw [cBlock_pos_iff M (j.val + 1) (by omega) (by omega)]
      exact hbelow (j.val + 1) (by omega) (by omega)
    rwa [hsj] at this
  -- hflat : rBlock = 0 on [q, b-2]  (Text boundaries [q+1, b-1] have no row-drop)
  have hflatB : ∀ j : Fin L, q ≤ j.val → j.val ≤ b - 2 → rBlock M j = 0 := by
    intro j hjlo hjhi
    have hnr : ¬ (Text M (tach M) ((j.val + 1) + 1) < Text M (tach M) (j.val + 1)) :=
      hqmax (j.val + 1) (by omega) (by omega)
    have hsj : (⟨(j.val + 1) - 1, by omega⟩ : Fin L) = j := by apply Fin.ext; simp only []; omega
    have hge : (0 : ℤ) ≤ rBlock M j := rBlock_nonneg M j
    have hle : ¬ (0 < rBlock M ⟨(j.val + 1) - 1, by omega⟩) := by
      rw [rBlock_pos_iff M (j.val + 1) (by omega) (by omega)]; exact hnr
    rw [hsj] at hle
    omega
  -- hcb : cBlock ⟨b-1⟩ = 0  (no col-drop at boundary b)
  have hcbB : cBlock M ⟨b - 1, hbm1L⟩ = 0 := by
    have hge : (0 : ℤ) ≤ cBlock M ⟨b - 1, hbm1L⟩ := cBlock_nonneg M _
    have hnc : ¬ (0 < cBlock M ⟨b - 1, hbm1L⟩) := by
      rw [cBlock_pos_iff M b (by omega) (by omega)]; exact hfail
    omega
  -- assemble: T' ∈ Adm, Mval T' = minAdm + (1 - r_q - c_q) ≤ minAdm - 1 < minAdm
  set T' := raiseTup M (q - 1) (b - 2) with hT'
  have hmem : T' ∈ Adm M := raiseTup_mem_Adm M q b hq1 hqb1 hbm1L hL hrowB hcolB
  have hval : Mval M T' = Mval M (tStar M)
      + (1 - rBlock M ⟨q - 1, by omega⟩ - cBlock M ⟨q - 1, by omega⟩) :=
    Mval_raiseTup M q b hq1 hb2 hqb1 hbm1L hflatB hcbB
  -- rBlock ⟨q-1⟩ ≥ 1 and cBlock ⟨q-1⟩ ≥ 1  (row-drop AND col-drop at q)
  have hr1 : (1 : ℤ) ≤ rBlock M ⟨q - 1, by omega⟩ := hrowB
  have hc1 : (1 : ℤ) ≤ cBlock M ⟨q - 1, by omega⟩ := by
    have : 0 < cBlock M ⟨q - 1, by omega⟩ :=
      (cBlock_pos_iff M q hq1 (by omega)).mpr (hbelow q hqlo hqhi)
    omega
  -- inf' ≤ Mval T', but Mval T' ≤ minAdm - 1 = Mval tStar - 1 < Mval tStar = inf'
  have hle : (Adm M).inf' (Adm_nonempty M) (Mval M) ≤ Mval M T' := Finset.inf'_le _ hmem
  rw [← Mval_tStar_eq_inf'] at hle
  -- hle : Mval M (tStar M) ≤ Mval M T'
  linarith [hval, hle, hr1, hc1]

/-! ## The whole-tail col-drop -/

/-- **The tail col-drops.** An interior both-drop at `s₀` forces the col-rank to drop at every tail
boundary `b ∈ [s₀, L−1]` — by strong induction on `b`, the first failure would trigger
`exchange_contra`. -/
theorem tail_colDrop (M : Fin (L + 1) → ℕ) (hL : 0 < L) (s₀ : ℕ)
    (hs₀1 : 1 ≤ s₀)
    (hrow₀ : Text M (tach M) (s₀ + 1) < Text M (tach M) s₀)
    (hcol₀ : Text M (tach M) (s₀ + 1) < Wext M s₀) :
    ∀ b, s₀ ≤ b → b ≤ L - 1 → Text M (tach M) (b + 1) < Wext M b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb₀ hbL
    by_contra hfail
    rcases eq_or_lt_of_le hb₀ with hbeq | hblt
    · -- b = s₀: contradicts the given col-drop
      rw [← hbeq] at hfail; exact hfail hcol₀
    · -- b > s₀: every boundary in [s₀, b-1] col-drops (IH), so exchange_contra applies
      refine exchange_contra M hL s₀ b hs₀1 hblt hbL hrow₀ ?_ hfail
      intro s hs_lo hs_hi
      exact ih s (by omega) (by omega) (by omega)

/-! ## The bridge -/

/-- **The hNo de-conditionalization bridge, ∀L.** For `0 < Wext M L`, an `M` with no interior-drop
has no interior both-drop. Lets the general-`L` clean/smeared achiever branches (which carry
`¬InteriorDrop`) supply the `NoInteriorBothDrop` the `minAdm` collapse needs. -/
theorem noInteriorBothDrop_of_not_interiorDrop
    (M : Fin (L + 1) → ℕ) (hWL : 0 < Wext M L) :
    ¬ InteriorDrop M → NoInteriorBothDrop M := by
  intro hNID s₀ hs₀1 hs₀L hboth
  -- prove NoInteriorBothDrop directly (contrapositive of the tail argument)
  obtain ⟨hrow₀, hcol₀⟩ := hboth
  have hL : 0 < L := by omega
  -- the both-drop at s₀ forces the whole tail [s₀, L-1] to col-drop
  have htail := tail_colDrop M hL s₀ hs₀1 hrow₀ hcol₀
  -- ...which is exactly InteriorDrop with witness p = s₀ — contradicting ¬InteriorDrop
  apply hNID
  refine ⟨hWL, s₀, hs₀1, hs₀L, hrow₀, ?_⟩
  intro c hc hcL
  exact htail c hc (by omega)

end DLNFibre.DLN.RLCT
