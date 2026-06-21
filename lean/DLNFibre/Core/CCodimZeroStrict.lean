import DLNFibre.Core.CCodimZeroMono

/-!
# `DLNFibre.Core.CCodimZeroStrict` — strict dimension-monotonicity of `cCodim · 0`

The strict, all-vertex companion of `Core.CCodimZeroMono.cCodim_zero_mono`:

* **`cCodim_zero_strict`**: `(∀ v, e v < e' v) → cCodim e 0 < cCodim e' 0`.

Discharging it makes the θ-count headline
(`Core.CCodimZeroMono.numTop_eq_ncard_topComponents_of_strict`) UNCONDITIONAL.

The route (Route B): reuse the four shortest-split moves and their `codimForm_*_le` ("≤ 0") sign
lemmas from `Core.CCodimZeroMono`, and upgrade one step to STRICT.

* **Lemma Y** (`codimForm_extendℤ_pos_of_fullCover`): full coverage (`1 ≤ e v` everywhere) ⟹ every
  corner-`0` Kostant partition has `codimForm ≥ 1`. Via the double-sum `codimForm = ∑ over interval
  pairs` and the extremal `[0,b]` coverage argument.
* **Lemma X** (`reduceStep_strict`): `codimForm ≥ 1` ⟹ a STRICT reduction step. Pick the active pair
  `(A, B)` minimising the shorter member's length; split the shorter member at the partner-adjacent
  vertex; the partner sits at coefficient exactly `−1` and "shortest covering" kills all positive
  coefficients, so `delta ≤ −1 < 0`.
* **Wiring**: the `+1`-step `cCodim e 0 < cCodim (e+1) 0`, then `e ≤ e+1 ≤ e'` + weak mono.

**Dependency rule:** `Core` only — no `DLN`, no field; over `ℤ`.
-/

namespace DLNFibre.Core

open Finset

universe u

variable {N : ℕ}

/-! ## The type-A pairing predicate on intervals

`pairBox A B` is the type-A `Ext`-pairing condition that `codimBil (boxℤ A) (boxℤ B) = 1`
(`Core.CCodimZeroMono.codimBil_boxℤ_boxℤ`): `A = [a,b]` is the *left* member, `B = [c,d]` the right.
On the box (`a ≤ b`, `c ≤ d`) it is `a < c ≤ b+1 ∧ b < d`. -/

/-- The type-A pairing predicate on a pair of `Fin`-intervals `A`, `B` (`A` left, `B` right):
`0 ≤ a, d ≤ N, a < c, c ≤ b+1, b < d` where `A = (a,b)`, `B = (c,d)`. -/
def pairBox (A B : Fin (N + 1) × Fin (N + 1)) : Prop :=
  (A.1 : ℤ) < (B.1 : ℤ) ∧ (B.1 : ℤ) ≤ (A.2 : ℤ) + 1 ∧ (A.2 : ℤ) < (B.2 : ℤ)

instance (A B : Fin (N + 1) × Fin (N + 1)) : Decidable (pairBox A B) := by
  unfold pairBox; infer_instance

/-! ## `codimForm (extendℤ m)` as a double sum over interval pairs

`codimBil` is biadditive, so pairing `extendℤ m` against itself, expanding the right slot as the
finite sum `∑_B m B · boxℤ B`, collapses each box-pairing to the existing right-rectangle
(`codimBil_extendℤ_boxℤ_right`). The result is the type-A double sum
`codimForm (extendℤ m) = ∑_A ∑_B (m A)(m B) · [pairBox A B]`. -/

/-- `codimBil` is additive over a `Finset.sum` in its right slot. -/
theorem codimBil_sum_right (A : ℤ → ℤ → ℤ) {ι : Type*} (s : Finset ι) (f : ι → ℤ → ℤ → ℤ) :
    codimBil N A (∑ b ∈ s, f b) = ∑ b ∈ s, codimBil N A (f b) := by
  classical
  induction s using Finset.induction with
  | empty => simp [codimBil]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, codimBil_add_right, ih]

/-- On the box, `extendℤ m` is the finite sum of its box indicators weighted by multiplicities:
`extendℤ m α β = ∑_B (m B : ℤ) · boxℤ B.1 B.2 α β` for `0 ≤ α ≤ β ≤ N`. -/
theorem extendℤ_eq_sum_boxℤ_onbox (m : Fin (N + 1) × Fin (N + 1) → ℕ) {α β : ℤ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ (N : ℤ)) :
    extendℤ m α β
      = ∑ B : Fin (N + 1) × Fin (N + 1), (m B : ℤ) * boxℤ (B.1 : ℤ) (B.2 : ℤ) α β := by
  -- the right side is `m (α,β)` (only the box `B = (α,β)` fires), matching `extendℤ` on the box
  set key : Fin (N + 1) × Fin (N + 1) := (⟨α.toNat, by omega⟩, ⟨β.toNat, by omega⟩) with hkey
  have hkα : α = ((key.1 : Fin (N + 1)) : ℤ) := by
    rw [hkey]; dsimp only; simp [Int.toNat_of_nonneg hα]
  have hkβ : β = ((key.2 : Fin (N + 1)) : ℤ) := by
    rw [hkey]; dsimp only; simp [Int.toNat_of_nonneg (le_trans hα hαβ)]
  have hsingle : (∑ B : Fin (N + 1) × Fin (N + 1), (m B : ℤ) * boxℤ (B.1 : ℤ) (B.2 : ℤ) α β)
      = (m key : ℤ) := by
    rw [Finset.sum_eq_single key]
    · unfold boxℤ; rw [if_pos ⟨hkα, hkβ⟩, mul_one]
    · intro B _ hBne
      have hbne : ¬ (α = (B.1 : ℤ) ∧ β = (B.2 : ℤ)) := by
        rintro ⟨h1, h2⟩
        refine hBne ?_
        rw [hkey, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
        dsimp only [Fin.val_mk]; omega
      unfold boxℤ; rw [if_neg hbne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ key) h
  rw [hsingle, extendℤ, dif_pos ⟨hα, hαβ, hβ⟩]

/-- `codimBil N A ·` reads its right argument only at box points `(u,v)` with `1 ≤ u ≤ v ≤ N`, so two
arrays agreeing on the box `{0 ≤ α ≤ β ≤ N}` give equal `codimBil N A`. -/
theorem codimBil_congr_onbox_right (A : ℤ → ℤ → ℤ) {f g : ℤ → ℤ → ℤ}
    (h : ∀ α β : ℤ, 0 ≤ α → α ≤ β → β ≤ (N : ℤ) → f α β = g α β) :
    codimBil N A f = codimBil N A g := by
  unfold codimBil
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun u hu ↦
    Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun v hv ↦ ?_
  rw [Finset.mem_Icc] at hi hu hj hv
  rw [h u v (by omega) (by omega) (by omega)]

/-- `codimBil` pulls a constant out of its right slot. -/
theorem codimBil_const_mul_right (A : ℤ → ℤ → ℤ) (c : ℤ) (B : ℤ → ℤ → ℤ) :
    codimBil N A (fun α β ↦ c * B α β) = c * codimBil N A B := by
  unfold codimBil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  ring

/-- `rrInd (B.1) (B.2) A`, on the box, is exactly the type-A pairing `pairBox A B` (`A` left, `B`
right). The `rrInd` clamp `1 ≤ B.1` follows from `A.1 < B.1` and `0 ≤ A.1`. -/
theorem rrInd_eq_pairBox (A B : Fin (N + 1) × Fin (N + 1)) :
    rrInd (B.1 : ℤ) (B.2 : ℤ) A ↔ pairBox A B := by
  unfold rrInd pairBox
  have h1 : (0 : ℤ) ≤ (A.1 : ℤ) := by positivity
  have h2 : (B.2 : ℤ) ≤ (N : ℤ) := by have := B.2.isLt; omega
  constructor
  · rintro ⟨_, _, hA1, hp, hA2⟩; exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨hac, hcb, hbd⟩; exact ⟨by omega, h2, by omega, by omega, by omega⟩

/-- **`codimForm` as the type-A double sum.** `codimForm (extendℤ m)
= ∑_A ∑_B (m A)(m B) · [pairBox A B]`. -/
theorem codimForm_extendℤ_eq_sum_pairs (m : Fin (N + 1) × Fin (N + 1) → ℕ) :
    codimForm N (extendℤ m)
      = ∑ A : Fin (N + 1) × Fin (N + 1), ∑ B : Fin (N + 1) × Fin (N + 1),
          (m A : ℤ) * (m B : ℤ) * (if pairBox A B then 1 else 0) := by
  -- replace the SECOND slot of `codimBil (extendℤ m) (extendℤ m)` by the box-sum on the box
  have hcong : codimForm N (extendℤ m)
      = codimBil N (extendℤ m)
          (∑ B : Fin (N + 1) × Fin (N + 1), fun α β ↦ (m B : ℤ) * boxℤ (B.1 : ℤ) (B.2 : ℤ) α β) := by
    rw [← codimBil_self]
    refine codimBil_congr_onbox_right (extendℤ m) (fun α β hα hαβ hβ ↦ ?_)
    rw [extendℤ_eq_sum_boxℤ_onbox m hα hαβ hβ, Finset.sum_apply, Finset.sum_apply]
  rw [hcong, codimBil_sum_right]
  -- each box term: `codimBil (extendℤ m) (m B • box B) = (m B) · ∑_{A : rrInd B} m A`
  -- gives `∑_B ∑_A (m B)(m A) [rrInd B A]`; swap the RHS and rewrite `rrInd B A = pairBox A B`
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ ↦ ?_
  rw [codimBil_const_mul_right, codimBil_extendℤ_boxℤ_right, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  -- `if rrInd B A then (m B)(m A) else 0  =  (m A)(m B)·[pairBox A B]`
  by_cases h : pairBox A B
  · rw [if_pos ((rrInd_eq_pairBox A B).mpr h), if_pos h]; ring
  · rw [if_neg (fun hh ↦ h ((rrInd_eq_pairBox A B).mp hh)), if_neg h]; ring

/-! ## Lemma Y: full coverage ⟹ `codimForm ≥ 1`

From the double sum: each term `(m A)(m B)·[pairBox A B] ≥ 0`, so `codimForm ≥ 0`, and `codimForm ≥ 1`
iff some active pair exists. Full coverage forces an active pair via the extremal `[0,b]` argument. -/

/-- A single term `(m A)(m B)·[pairBox A B]` of the double sum is nonnegative. -/
theorem pair_term_nonneg (m : Fin (N + 1) × Fin (N + 1) → ℕ)
    (A B : Fin (N + 1) × Fin (N + 1)) :
    0 ≤ (m A : ℤ) * (m B : ℤ) * (if pairBox A B then 1 else 0) := by
  refine mul_nonneg (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) ?_
  split_ifs <;> norm_num

/-- **`∃ active pair ⟹ `codimForm ≥ 1`.** If active intervals `A`, `B` (`m A ≥ 1`, `m B ≥ 1`) form a
pair (`pairBox A B`), then `codimForm (extendℤ m) ≥ 1`: the `(A,B)`-term of the double sum is `≥ 1`
and every term is nonnegative. -/
theorem codimForm_extendℤ_pos_of_exists_pair {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    {A B : Fin (N + 1) × Fin (N + 1)} (hA : 1 ≤ m A) (hB : 1 ≤ m B) (hpair : pairBox A B) :
    1 ≤ codimForm N (extendℤ m) := by
  rw [codimForm_extendℤ_eq_sum_pairs]
  -- bound the whole double sum below by its single `(A,B)`-term
  have hterm : (1 : ℤ) ≤ (m A : ℤ) * (m B : ℤ) * (if pairBox A B then 1 else 0) := by
    rw [if_pos hpair, mul_one]
    have : (1 : ℤ) * 1 ≤ (m A : ℤ) * (m B : ℤ) :=
      mul_le_mul (by exact_mod_cast hA) (by exact_mod_cast hB) (by norm_num) (by positivity)
    linarith
  calc (1 : ℤ) ≤ (m A : ℤ) * (m B : ℤ) * (if pairBox A B then 1 else 0) := hterm
    _ = ∑ B' : Fin (N + 1) × Fin (N + 1),
          (m A : ℤ) * (m B' : ℤ) * (if pairBox A B' then 1 else 0)
          - ∑ B' ∈ Finset.univ.erase B,
              (m A : ℤ) * (m B' : ℤ) * (if pairBox A B' then 1 else 0) := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ B)]; ring
    _ ≤ ∑ B' : Fin (N + 1) × Fin (N + 1),
          (m A : ℤ) * (m B' : ℤ) * (if pairBox A B' then 1 else 0) := by
        have : 0 ≤ ∑ B' ∈ Finset.univ.erase B,
            (m A : ℤ) * (m B' : ℤ) * (if pairBox A B' then 1 else 0) :=
          Finset.sum_nonneg fun B' _ ↦ pair_term_nonneg m A B'
        linarith
    _ ≤ ∑ A' : Fin (N + 1) × Fin (N + 1), ∑ B' : Fin (N + 1) × Fin (N + 1),
          (m A' : ℤ) * (m B' : ℤ) * (if pairBox A' B' then 1 else 0) := by
        have hrow : ∀ A', 0 ≤ ∑ B' : Fin (N + 1) × Fin (N + 1),
            (m A' : ℤ) * (m B' : ℤ) * (if pairBox A' B' then 1 else 0) :=
          fun A' ↦ Finset.sum_nonneg fun B' _ ↦ pair_term_nonneg m A' B'
        refine Finset.single_le_sum (f := fun A' ↦ ∑ B' : Fin (N + 1) × Fin (N + 1),
            (m A' : ℤ) * (m B' : ℤ) * (if pairBox A' B' then 1 else 0))
          (fun A' _ ↦ hrow A') (Finset.mem_univ A)

/-- **`codimForm ≥ 1 ⟹ ∃ active pair`.** If `codimForm (extendℤ m) ≥ 1` then some active intervals
`A`, `B` (`m A ≥ 1`, `m B ≥ 1`) form a pair (`pairBox A B`). Contrapositive: no active pair makes
every double-sum term `0`. -/
theorem exists_pair_of_codimForm_pos {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hpos : 1 ≤ codimForm N (extendℤ m)) :
    ∃ A B : Fin (N + 1) × Fin (N + 1), 1 ≤ m A ∧ 1 ≤ m B ∧ pairBox A B := by
  by_contra hno
  push_neg at hno
  -- no active pair ⟹ each double-sum term is `0`
  have hzero : codimForm N (extendℤ m) = 0 := by
    rw [codimForm_extendℤ_eq_sum_pairs]
    refine Finset.sum_eq_zero fun A _ ↦ Finset.sum_eq_zero fun B _ ↦ ?_
    by_cases hpair : pairBox A B
    · -- a pair forces `m A = 0` or `m B = 0`
      rcases Nat.eq_zero_or_pos (m A) with hA | hA
      · rw [hA]; simp
      · have : m B = 0 := by
          by_contra hB
          exact hno A B hA (Nat.one_le_iff_ne_zero.mpr hB) hpair
        rw [this]; simp
    · rw [if_neg hpair]; ring
  omega

/-- A vertex `k` with positive value in a Kostant partition is covered by an active interval. -/
theorem exists_active_covering {e : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hm : m ∈ kostantPartitions e 0) {k : Fin (N + 1)} (hk : 1 ≤ e k) :
    ∃ p : Fin (N + 1) × Fin (N + 1), 1 ≤ m p ∧ p.1 ≤ k ∧ k ≤ p.2 := by
  obtain ⟨-, -, hkost, -⟩ := mem_kostantPartitions.mp hm
  by_contra hno
  push_neg at hno
  have : e k = 0 := by
    rw [hkost k, Finset.sum_eq_zero]
    intro p hp; rw [Finset.mem_filter] at hp
    by_contra hmp
    exact absurd (hno p (Nat.one_le_iff_ne_zero.mpr hmp) hp.2.1) (not_lt.mpr hp.2.2)
  omega

/-- **Lemma Y: full coverage ⟹ `codimForm ≥ 1`.** If `e v ≥ 1` at every vertex and `m` is a corner-`0`
Kostant partition of `e`, then `codimForm (extendℤ m) ≥ 1`. The extremal `[0,b]` argument: take the
longest active `[0,b]`; corner-`0` gives `b < N`, so vertex `b+1` exists and is covered by an active
`[c,d]`; maximality forces `c ≥ 1`, so `[0,b] → [c,d]` is a type-A pair. -/
theorem codimForm_extendℤ_pos_of_fullCover {e : Fin (N + 1) → ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions e 0)
    (hfull : ∀ v, 1 ≤ e v) :
    1 ≤ codimForm N (extendℤ m) := by
  classical
  obtain ⟨-, -, -, hc0⟩ := mem_kostantPartitions.mp hm
  -- active intervals of the form `(0, q)` covering vertex `0`
  set T : Finset (Fin (N + 1)) :=
    Finset.univ.filter (fun q ↦ 1 ≤ m ((0 : Fin (N + 1)), q)) with hT
  have hTne : T.Nonempty := by
    obtain ⟨p, hp1, hp2, hp3⟩ := exists_active_covering hm (hfull 0)
    have hp10 : p.1 = (0 : Fin (N + 1)) := le_antisymm hp2 (Fin.zero_le _)
    refine ⟨p.2, by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [← hp10]; exact hp1⟩⟩
  -- take the largest such `b`
  obtain ⟨b, hbT, hbmax⟩ := T.exists_max_image (fun q ↦ (q : ℕ)) hTne
  rw [hT, Finset.mem_filter] at hbT
  have hb_active : 1 ≤ m ((0 : Fin (N + 1)), b) := hbT.2
  -- `b < N`: else `(0, b) = (0, last N)` is the corner with `m = 0`
  have hbN : (b : ℕ) < N := by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp b.isLt) with h | h
    · exact h
    · exfalso
      have hbl : b = Fin.last N := Fin.ext (by rw [Fin.val_last]; omega)
      rw [hbl, hc0] at hb_active; exact absurd hb_active (by norm_num)
  -- vertex `b+1` exists and is covered by an active `(c, d)`
  set k1 : Fin (N + 1) := ⟨(b : ℕ) + 1, by omega⟩ with hk1
  obtain ⟨⟨c, d⟩, hcd_active, hc_le, hk_le⟩ := exists_active_covering hm (hfull k1)
  -- `c ≥ 1`: else `(0, d)` is active with `d > b`, contradicting maximality
  have hc_pos : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with hc0' | hc0'
    · exfalso
      have hc_eq : c = (0 : Fin (N + 1)) := Fin.ext (by rw [Fin.val_zero]; omega)
      have hdT : d ∈ T := by
        rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [← hc_eq]; exact hcd_active⟩
      have hdk : (k1 : ℕ) ≤ (d : ℕ) := Fin.le_def.mp hk_le
      have hmaxd := hbmax d hdT
      simp only [hk1] at hdk
      omega
    · exact hc0'
  -- the type-A pair `[0,b] → [c,d]`
  refine codimForm_extendℤ_pos_of_exists_pair hb_active hcd_active ?_
  have hck1 : (c : ℕ) ≤ (b : ℕ) + 1 := by have := Fin.le_def.mp hc_le; simp only [hk1] at this; omega
  have hbd : (b : ℕ) < (d : ℕ) := by have := Fin.le_def.mp hk_le; simp only [hk1] at this; omega
  unfold pairBox
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fin.val_zero]; exact_mod_cast hc_pos
  · push_cast; exact_mod_cast hck1
  · exact_mod_cast hbd

/-! ## The strict split delta: a present partner at coefficient `−1`

The `codimForm_*_le` sign lemmas of `Core.CCodimZeroMono` bound the split delta `∑_Y m̄ Y · coeff Y`
by `0` (positive coeffs killed by minimality). The strict upgrade: a *present* partner interval `B`
(`m B ≥ 1`) at coefficient `≤ −1` forces `∑ ≤ −1`. The generic sum lemma below feeds each move's
`coeff`/`_pos_imp` plus the partner. -/

/-- **Generic strict sum bound.** If every interval with a *positive* coefficient has multiplicity `0`
(minimality kills positives) and some present interval `B` (`m B ≥ 1`) has coefficient `≤ −1`, then
`∑_Y m̄ Y · coeff Y ≤ −1`. -/
theorem sum_coeff_le_neg_one (m : Fin (N + 1) × Fin (N + 1) → ℕ)
    (coeff : Fin (N + 1) × Fin (N + 1) → ℤ)
    (hkill : ∀ Y, 0 < coeff Y → m Y = 0)
    {B : Fin (N + 1) × Fin (N + 1)} (hB : 1 ≤ m B) (hBc : coeff B ≤ -1) :
    ∑ Y : Fin (N + 1) × Fin (N + 1), (m Y : ℤ) * coeff Y ≤ -1 := by
  classical
  -- each summand is `≤ 0`
  have hnonpos : ∀ Y, (m Y : ℤ) * coeff Y ≤ 0 := by
    intro Y
    rcases lt_or_ge 0 (coeff Y) with hc | hc
    · rw [hkill Y hc]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hc
  -- the `B`-summand is `≤ −1`
  have hBterm : (m B : ℤ) * coeff B ≤ -1 := by
    calc (m B : ℤ) * coeff B ≤ (m B : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left hBc (Int.natCast_nonneg _)
      _ ≤ 1 * (-1) := by
          have : (1 : ℤ) ≤ (m B : ℤ) := by exact_mod_cast hB
          nlinarith
      _ = -1 := by ring
  -- split off the `B`-summand; the rest is `≤ 0`
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ B)]
  have hrest : ∑ Y ∈ Finset.univ.erase B, (m Y : ℤ) * coeff Y ≤ 0 :=
    Finset.sum_nonpos fun Y _ ↦ hnonpos Y
  linarith

/-! ### Partner coefficients are `≤ −1` (`omega` on the indicator combinations)

When the split source `[a,d']` is the LEFT member of a pair `pairBox (a,d') B`, the split at the
partner-adjacent vertex assigns `B` coefficient exactly `−1`; symmetrically when `[a,d']` is the
RIGHT member of `pairBox A (a,d')`, the partner `A` gets `−1`. Each is `omega` on the unfolded
`rrInd`/`llInd` indicators plus the `pairBox`/`c = b+2` (resp endpoint) relations. -/

/-- Interior split: the partner `[c, B2]` (with `d' < B2`, where `c = b+2` is the right split-piece
endpoint) sits at `splitCoeff a b c d' (c, B2) = −1`. -/
theorem splitCoeff_partner_le {a b c d' B2 : Fin (N + 1)} (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 2)
    (hcd : (c : ℕ) ≤ d') (hB2 : (d' : ℕ) < B2) :
    splitCoeff a b c d' (c, B2) ≤ -1 := by
  have hcZ : (c : ℤ) = (b : ℤ) + 2 := by exact_mod_cast hbc
  have habZ : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hcdZ : (c : ℤ) ≤ d' := by exact_mod_cast hcd
  have hB2Z : (d' : ℤ) < B2 := by exact_mod_cast hB2
  have hB2N : (B2 : ℤ) ≤ (N : ℤ) := by have := B2.isLt; omega
  have hcN : (c : ℤ) ≤ (N : ℤ) := by have := c.isLt; omega
  have haN : (a : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
  have hbN : (b : ℤ) ≤ (N : ℤ) := by have := b.isLt; omega
  have hdN : (d' : ℤ) ≤ (N : ℤ) := by have := d'.isLt; omega
  have hcnn : (0 : ℤ) ≤ (c : ℤ) := by positivity
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  unfold splitCoeff rrInd llInd
  dsimp only
  split_ifs <;> omega

/-- Left-shrink: the partner `[c, B2]` (with `d' < B2`, `c = a+1`) sits at
`leftCoeff a c d' (c, B2) = −1` (split at the left endpoint `a`). -/
theorem leftCoeff_partner_le {a c d' B2 : Fin (N + 1)} (hac : (c : ℕ) = a + 1)
    (hcd : (c : ℕ) ≤ d') (hB2 : (d' : ℕ) < B2) :
    leftCoeff a c d' (c, B2) ≤ -1 := by
  have hcZ : (c : ℤ) = (a : ℤ) + 1 := by exact_mod_cast hac
  have hcdZ : (c : ℤ) ≤ d' := by exact_mod_cast hcd
  have hB2Z : (d' : ℤ) < B2 := by exact_mod_cast hB2
  have hB2N : (B2 : ℤ) ≤ (N : ℤ) := by have := B2.isLt; omega
  have hcN : (c : ℤ) ≤ (N : ℤ) := by have := c.isLt; omega
  have haN : (a : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
  have hdN : (d' : ℤ) ≤ (N : ℤ) := by have := d'.isLt; omega
  have hcnn : (0 : ℤ) ≤ (c : ℤ) := by positivity
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  unfold leftCoeff rrInd llInd
  dsimp only
  split_ifs <;> omega

/-- Right-shrink: the partner `[A1, b]` (with `A1 < a`, `b = d'−1`) sits at
`rightCoeff a b d' (A1, b) = −1` (split at the right endpoint `d'`). -/
theorem rightCoeff_partner_le {a b d' A1 : Fin (N + 1)} (hab : (a : ℕ) ≤ b)
    (hbd : (b : ℕ) + 1 = d') (hA1 : (A1 : ℕ) < a) :
    rightCoeff a b d' (A1, b) ≤ -1 := by
  have hbdZ : (b : ℤ) + 1 = d' := by exact_mod_cast hbd
  have habZ : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hA1Z : (A1 : ℤ) < a := by exact_mod_cast hA1
  have hA1N : (A1 : ℤ) ≤ (N : ℤ) := by have := A1.isLt; omega
  have haN : (a : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
  have hbN : (b : ℤ) ≤ (N : ℤ) := by have := b.isLt; omega
  have hA1nn : (0 : ℤ) ≤ (A1 : ℤ) := by positivity
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  unfold rightCoeff rrInd llInd
  dsimp only
  split_ifs <;> omega

/-! ### The four strict `_lt` move deltas (`codimForm` drops by `≥ 1`)

Each upgrades the corresponding `Core.CCodimZeroMono.codimForm_*_le` ("≤ 0") to "≤ −1", consuming the
same shortest-covering hypothesis `hshort` (kills positive coefficients) plus a *present* partner
interval at coefficient `≤ −1`. -/

/-- **Interior `redMove` strict.** `[a,d']` shortest covering `k = b+1` (`c = b+2`) and *any* present
partner `P` at `splitCoeff ≤ −1` ⟹ `codimForm` drops by at least `1`. -/
theorem codimForm_redMove_lt (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b c d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 2) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d'))
    (hshort : ∀ Y : Fin (N + 1) × Fin (N + 1), 1 ≤ m Y →
      (Y.1 : ℤ) ≤ (b : ℤ) + 1 → (b : ℤ) + 1 ≤ (Y.2 : ℤ) →
      (d' : ℤ) - (a : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ))
    {P : Fin (N + 1) × Fin (N + 1)} (hPpres : 1 ≤ m P) (hPc : splitCoeff a b c d' P ≤ -1) :
    codimForm N (extendℤ (redMove m a b c d')) ≤ codimForm N (extendℤ m) - 1 := by
  rw [codimForm_redMove m hab (by omega) hcd hsad]
  have hkill : ∀ Y, 0 < splitCoeff a b c d' Y → m Y = 0 := by
    intro Y hc'
    obtain ⟨⟨h1, h2⟩, hlen⟩ := splitCoeff_pos_imp hab hbc hcd hc'
    by_contra hne
    exact absurd (hshort Y (Nat.one_le_iff_ne_zero.mpr hne) h1 h2) (not_le.mpr hlen)
  have := sum_coeff_le_neg_one m (splitCoeff a b c d') hkill hPpres hPc
  linarith

/-- **`leftShrink` strict.** `[a,d']` shortest covering its left endpoint `a` (`c = a+1`) and *any*
present partner `P` at `leftCoeff ≤ −1` ⟹ `codimForm` drops by at least `1`. -/
theorem codimForm_leftShrink_lt (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a c d' : Fin (N + 1)}
    (hac : (c : ℕ) = a + 1) (hcd : (c : ℕ) ≤ d') (hsad : 1 ≤ m (a, d'))
    (hshort : ∀ Y : Fin (N + 1) × Fin (N + 1), 1 ≤ m Y →
      (Y.1 : ℤ) ≤ (a : ℤ) → (a : ℤ) ≤ (Y.2 : ℤ) →
      (d' : ℤ) - (a : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ))
    {P : Fin (N + 1) × Fin (N + 1)} (hPpres : 1 ≤ m P) (hPc : leftCoeff a c d' P ≤ -1) :
    codimForm N (extendℤ (leftShrink m a c d')) ≤ codimForm N (extendℤ m) - 1 := by
  rw [codimForm_leftShrink m (by omega) hcd hsad]
  have hkill : ∀ Y, 0 < leftCoeff a c d' Y → m Y = 0 := by
    intro Y hc'
    obtain ⟨⟨h1, h2⟩, hlen⟩ := leftCoeff_pos_imp hac hcd hc'
    by_contra hne
    exact absurd (hshort Y (Nat.one_le_iff_ne_zero.mpr hne) h1 h2) (not_le.mpr hlen)
  have := sum_coeff_le_neg_one m (leftCoeff a c d') hkill hPpres hPc
  linarith

/-- **`rightShrink` strict.** `[a,d']` shortest covering its right endpoint `d'` (`b = d'−1`) and *any*
present partner `P` at `rightCoeff ≤ −1` ⟹ `codimForm` drops by at least `1`. -/
theorem codimForm_rightShrink_lt (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b d' : Fin (N + 1)}
    (hab : (a : ℕ) ≤ b) (hbd : (b : ℕ) + 1 = d') (hsad : 1 ≤ m (a, d'))
    (hshort : ∀ Y : Fin (N + 1) × Fin (N + 1), 1 ≤ m Y →
      (Y.1 : ℤ) ≤ (d' : ℤ) → (d' : ℤ) ≤ (Y.2 : ℤ) →
      (d' : ℤ) - (a : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ))
    {P : Fin (N + 1) × Fin (N + 1)} (hPpres : 1 ≤ m P) (hPc : rightCoeff a b d' P ≤ -1) :
    codimForm N (extendℤ (rightShrink m a b d')) ≤ codimForm N (extendℤ m) - 1 := by
  rw [codimForm_rightShrink m hab (by omega) hsad]
  have hkill : ∀ Y, 0 < rightCoeff a b d' Y → m Y = 0 := by
    intro Y hc'
    obtain ⟨⟨h1, h2⟩, hlen⟩ := rightCoeff_pos_imp hab hbd hc'
    by_contra hne
    exact absurd (hshort Y (Nat.one_le_iff_ne_zero.mpr hne) h1 h2) (not_le.mpr hlen)
  have := sum_coeff_le_neg_one m (rightCoeff a b d') hkill hPpres hPc
  linarith

/-- Singleton removal, LEFT-member case: the partner `[a+1, B2]` (`a < B2`, `a < N`) sits at
`removeCoeff a (a+1, B2) = −1` (the `llInd a a` indicator fires). -/
theorem removeCoeff_partner_left_le {a c B2 : Fin (N + 1)} (hac : (c : ℕ) = a + 1)
    (haN : (a : ℕ) < N) (hB2 : (a : ℕ) < B2) :
    removeCoeff a (c, B2) ≤ -1 := by
  have hcZ : (c : ℤ) = (a : ℤ) + 1 := by exact_mod_cast hac
  have haNZ : (a : ℤ) < (N : ℤ) := by exact_mod_cast haN
  have hB2Z : (a : ℤ) < B2 := by exact_mod_cast hB2
  have hB2N : (B2 : ℤ) ≤ (N : ℤ) := by have := B2.isLt; omega
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  have hcnn : (0 : ℤ) ≤ (c : ℤ) := by positivity
  unfold removeCoeff rrInd llInd
  dsimp only
  split_ifs <;> omega

/-- Singleton removal, RIGHT-member case: the partner `[A1, a−1]` (`A1 < a`, `0 < a`) sits at
`removeCoeff a (A1, b) = −1` (the `rrInd a a` indicator fires), where `b = a−1`. -/
theorem removeCoeff_partner_right_le {a b A1 : Fin (N + 1)} (hba : (b : ℕ) + 1 = a)
    (hA1 : (A1 : ℕ) < a) :
    removeCoeff a (A1, b) ≤ -1 := by
  have hbaZ : (b : ℤ) + 1 = a := by exact_mod_cast hba
  have hA1Z : (A1 : ℤ) < a := by exact_mod_cast hA1
  have hA1N : (A1 : ℤ) ≤ (N : ℤ) := by have := A1.isLt; omega
  have haN : (a : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  have hA1nn : (0 : ℤ) ≤ (A1 : ℤ) := by positivity
  unfold removeCoeff rrInd llInd
  dsimp only
  split_ifs <;> omega

/-- Interior split, LEFT-partner case: the partner `[A1, b]` (with `A1 < a`, where `b = k−1` is the
left split-piece endpoint) sits at `splitCoeff a b c d' (A1, b) = −1`. -/
theorem splitCoeff_partner_left_le {a b c d' A1 : Fin (N + 1)} (hab : (a : ℕ) ≤ b) (hbc : (c : ℕ) = b + 2)
    (hcd : (c : ℕ) ≤ d') (hA1 : (A1 : ℕ) < a) :
    splitCoeff a b c d' (A1, b) ≤ -1 := by
  have hcZ : (c : ℤ) = (b : ℤ) + 2 := by exact_mod_cast hbc
  have habZ : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hcdZ : (c : ℤ) ≤ d' := by exact_mod_cast hcd
  have hA1Z : (A1 : ℤ) < a := by exact_mod_cast hA1
  have hA1N : (A1 : ℤ) ≤ (N : ℤ) := by have := A1.isLt; omega
  have haN : (a : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
  have hbN : (b : ℤ) ≤ (N : ℤ) := by have := b.isLt; omega
  have hdN : (d' : ℤ) ≤ (N : ℤ) := by have := d'.isLt; omega
  have hA1nn : (0 : ℤ) ≤ (A1 : ℤ) := by positivity
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  unfold splitCoeff rrInd llInd
  dsimp only
  split_ifs <;> omega

/-- Left-shrink, LEFT-partner case: the partner `[A1, b]` (with `A1 < a`, `b = a−1`, `c = a+1`) sits at
`leftCoeff a c d' (A1, b) = −1`. -/
theorem leftCoeff_partner_left_le {a c d' A1 b : Fin (N + 1)} (hac : (c : ℕ) = a + 1)
    (hcd : (c : ℕ) ≤ d') (hba : (b : ℕ) + 1 = a) (hA1 : (A1 : ℕ) < a) :
    leftCoeff a c d' (A1, b) ≤ -1 := by
  have hcZ : (c : ℤ) = (a : ℤ) + 1 := by exact_mod_cast hac
  have hcdZ : (c : ℤ) ≤ d' := by exact_mod_cast hcd
  have hbaZ : (b : ℤ) + 1 = a := by exact_mod_cast hba
  have hA1Z : (A1 : ℤ) < a := by exact_mod_cast hA1
  have hA1N : (A1 : ℤ) ≤ (N : ℤ) := by have := A1.isLt; omega
  have haN : (a : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
  have hbN : (b : ℤ) ≤ (N : ℤ) := by have := b.isLt; omega
  have hdN : (d' : ℤ) ≤ (N : ℤ) := by have := d'.isLt; omega
  have hA1nn : (0 : ℤ) ≤ (A1 : ℤ) := by positivity
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  unfold leftCoeff rrInd llInd
  dsimp only
  split_ifs <;> omega

/-- Right-shrink, RIGHT-partner case: the partner `[c, B2]` (with `d' < B2`, `c = d'+1`, `b = d'−1`)
sits at `rightCoeff a b d' (c, B2) = −1`. -/
theorem rightCoeff_partner_right_le {a b d' c B2 : Fin (N + 1)} (hab : (a : ℕ) ≤ b)
    (hbd : (b : ℕ) + 1 = d') (hcd : (c : ℕ) = d' + 1) (hB2 : (d' : ℕ) < B2) :
    rightCoeff a b d' (c, B2) ≤ -1 := by
  have hbdZ : (b : ℤ) + 1 = d' := by exact_mod_cast hbd
  have habZ : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hcdZ : (c : ℤ) = (d' : ℤ) + 1 := by exact_mod_cast hcd
  have hB2Z : (d' : ℤ) < B2 := by exact_mod_cast hB2
  have hB2N : (B2 : ℤ) ≤ (N : ℤ) := by have := B2.isLt; omega
  have hcN : (c : ℤ) ≤ (N : ℤ) := by have := c.isLt; omega
  have haN : (a : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
  have hbN : (b : ℤ) ≤ (N : ℤ) := by have := b.isLt; omega
  have hcnn : (0 : ℤ) ≤ (c : ℤ) := by positivity
  have hann : (0 : ℤ) ≤ (a : ℤ) := by positivity
  unfold rightCoeff rrInd llInd
  dsimp only
  split_ifs <;> omega

/-- **`removeMove` strict.** Singleton `[a,a]` present, plus a present partner at coefficient `≤ −1`
(either `[a+1,B2]` with `a < B2`, `a < N`, or `[A1,a−1]` with `A1 < a`) ⟹ `codimForm` drops by at
least `1`. The shortest-covering hypothesis is automatic: a singleton has length `0`. -/
theorem codimForm_removeMove_lt (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a : Fin (N + 1)}
    (hsa : 1 ≤ m (a, a)) {P : Fin (N + 1) × Fin (N + 1)} (hPpres : 1 ≤ m P)
    (hPc : removeCoeff a P ≤ -1) :
    codimForm N (extendℤ (removeMove m a)) ≤ codimForm N (extendℤ m) - 1 := by
  rw [codimForm_removeMove m hsa]
  have hkill : ∀ Y, 0 < removeCoeff a Y → m Y = 0 := fun Y hc' ↦
    absurd hc' (not_lt.mpr (removeCoeff_nonpos a Y))
  have := sum_coeff_le_neg_one m (removeCoeff a) hkill hPpres hPc
  linarith

/-! ## Lemma X: the strict reduction step

`codimForm ≥ 1` gives an active pair. Among active pairs, take one `(A*,B*)` minimising the shorter
member's length `min(len A, len B)`; let `I` be the shorter member. ClaimA: `I` is a shortest active
covering interval of the partner-adjacent vertex `k`. Then the split of `I` at `k` (the appropriate
atomic move) has the partner at coefficient `−1`, so `codimForm` drops by `≥ 1`. -/

/-- The active pairs of `m`, as a `Finset` of `(A, B)` with `m A ≥ 1`, `m B ≥ 1`, `pairBox A B`. -/
def activePairs (m : Fin (N + 1) × Fin (N + 1) → ℕ) :
    Finset ((Fin (N + 1) × Fin (N + 1)) × (Fin (N + 1) × Fin (N + 1))) :=
  Finset.univ.filter (fun AB ↦ 1 ≤ m AB.1 ∧ 1 ≤ m AB.2 ∧ pairBox AB.1 AB.2)

/-- The length of an interval `[x,y]` as an integer `y − x ≥ 0`. -/
def ilen (Y : Fin (N + 1) × Fin (N + 1)) : ℤ := (Y.2 : ℤ) - (Y.1 : ℤ)

/-- **ClaimA (left-member case).** If `(A*, B*)` minimises `min(ilen A, ilen B)` over active pairs and
`ilen A* ≤ ilen B*`, then `A* = [a,d']` is a shortest active covering interval of `k = c−1` (where
`B* = [c, d]`): any active `Y` covering `k` is at least as long as `A*`. -/
theorem claimA_left {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    {a d' c d : Fin (N + 1)} (hAact : 1 ≤ m (a, d')) (hBact : 1 ≤ m (c, d))
    (hpair : pairBox (a, d') (c, d)) (hshorter : ilen (a, d') ≤ ilen (c, d))
    (hmin : ∀ P Q : Fin (N + 1) × Fin (N + 1), 1 ≤ m P → 1 ≤ m Q → pairBox P Q →
      min (ilen (a, d')) (ilen (c, d)) ≤ min (ilen P) (ilen Q))
    {Y : Fin (N + 1) × Fin (N + 1)} (hYact : 1 ≤ m Y)
    (hYcov1 : (Y.1 : ℤ) ≤ (c : ℤ) - 1) (hYcov2 : (c : ℤ) - 1 ≤ (Y.2 : ℤ)) :
    (d' : ℤ) - (a : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ) := by
  unfold pairBox at hpair; unfold ilen at hshorter hmin
  obtain ⟨hp1, hp2, hp3⟩ := hpair; dsimp only at hp1 hp2 hp3
  -- the LHS min collapses to `ilen A* = d' − a` (since `A*` is the shorter member)
  rw [min_eq_left hshorter] at hmin
  by_contra hlt
  push_neg at hlt
  -- `Y = [x,y]` covers `k = c−1`, shorter than `A* = [a,d']`. Split on `y < d`.
  rcases lt_or_ge (Y.2 : ℤ) (d : ℤ) with hyd | hyd
  · -- `pair(Y, B*)`: shorter min ⟹ contradiction
    have hYpair : pairBox Y (c, d) := by
      unfold pairBox; dsimp only; omega
    have hchain : (d' : ℤ) - a ≤ (Y.2 : ℤ) - Y.1 :=
      le_trans (hmin Y (c, d) hYact hBact hYpair) (min_le_left _ _)
    omega
  · -- `pair(A*, Y)`: `a < x` from the length bound; shorter min ⟹ contradiction
    have hYpair : pairBox (a, d') Y := by
      unfold pairBox; dsimp only; omega
    have hchain : (d' : ℤ) - a ≤ (Y.2 : ℤ) - Y.1 :=
      le_trans (hmin (a, d') Y hAact hYact hYpair) (min_le_right _ _)
    omega

/-- **ClaimA (right-member case).** If `(A*, B*)` minimises `min(ilen A, ilen B)` and
`ilen B* < ilen A*`, then `B* = [a,d']` is a shortest active covering interval of `k = b+1` (where
`A* = [c, b]`): any active `Y` covering `k` is at least as long as `B*`. -/
theorem claimA_right {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    {c b a d' : Fin (N + 1)} (hAact : 1 ≤ m (c, b)) (hBact : 1 ≤ m (a, d'))
    (hpair : pairBox (c, b) (a, d')) (hshorter : ilen (a, d') < ilen (c, b))
    (hmin : ∀ P Q : Fin (N + 1) × Fin (N + 1), 1 ≤ m P → 1 ≤ m Q → pairBox P Q →
      min (ilen (c, b)) (ilen (a, d')) ≤ min (ilen P) (ilen Q))
    {Y : Fin (N + 1) × Fin (N + 1)} (hYact : 1 ≤ m Y)
    (hYcov1 : (Y.1 : ℤ) ≤ (b : ℤ) + 1) (hYcov2 : (b : ℤ) + 1 ≤ (Y.2 : ℤ)) :
    (d' : ℤ) - (a : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ) := by
  unfold pairBox at hpair; unfold ilen at hshorter hmin
  obtain ⟨hp1, hp2, hp3⟩ := hpair; dsimp only at hp1 hp2 hp3
  -- the LHS min collapses to `ilen B* = d' − a` (since `B*` is the strictly shorter member)
  rw [min_eq_right (le_of_lt hshorter)] at hmin
  by_contra hlt
  push_neg at hlt
  -- `Y = [x,y]` covers `k = b+1`, shorter than `B* = [a,d']`. Split on `c < x` (`c = A*.1`).
  rcases lt_or_ge (c : ℤ) (Y.1 : ℤ) with hcx | hcx
  · -- `pair(A*, Y)`
    have hYpair : pairBox (c, b) Y := by
      unfold pairBox; dsimp only; omega
    have hchain : (d' : ℤ) - a ≤ (Y.2 : ℤ) - Y.1 :=
      le_trans (hmin (c, b) Y hAact hYact hYpair) (min_le_right _ _)
    omega
  · -- `pair(Y, B*)`: `x < a` from `x ≤ c < a`; `y < d'` from the length bound
    have hYpair : pairBox Y (a, d') := by
      unfold pairBox; dsimp only; omega
    have hchain : (d' : ℤ) - a ≤ (Y.2 : ℤ) - Y.1 :=
      le_trans (hmin Y (a, d') hYact hBact hYpair) (min_le_left _ _)
    omega

/-! ## The strict reduction step and the `+1` step

`reduceStep_strict`: at a corner-`0` partition `m` of `e` with `codimForm ≥ 1`, there is a vertex `k`
(with `1 ≤ e k`) and a corner-`0` partition `m''` of `e` decremented at `k` whose `codimForm` is at
least `1` smaller. Then the `+1`-step `cCodim e 0 < cCodim (e+1) 0` follows from Lemma Y (the minimiser
of `e+1` has `codimForm ≥ 1`) + the strict step + the LANDED weak monotonicity. -/

/-- **The strict reduction step (Lemma X).** If `m ∈ kostantPartitions e 0` and
`codimForm (extendℤ m) ≥ 1`, there is a vertex `k` with `1 ≤ e k` and `m'' ∈ kostantPartitions
(Function.update e k (e k - 1)) 0` with `codimForm (extendℤ m'') ≤ codimForm (extendℤ m) - 1`. -/
theorem reduceStep_strict {e : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hm : m ∈ kostantPartitions e 0) (hpos : 1 ≤ codimForm N (extendℤ m)) :
    ∃ k : Fin (N + 1), 1 ≤ e k ∧ ∃ m'' ∈ kostantPartitions (Function.update e k (e k - 1)) 0,
      codimForm N (extendℤ m'') ≤ codimForm N (extendℤ m) - 1 := by
  classical
  obtain ⟨hbnd, hsupp, hkost, hc0⟩ := mem_kostantPartitions.mp hm
  -- select a minimal-shorter-member active pair
  obtain ⟨A, B, hAB1, hAB2, hABp⟩ := exists_pair_of_codimForm_pos hpos
  have hABmem : (A, B) ∈ activePairs m := by
    rw [activePairs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hAB1, hAB2, hABp⟩
  obtain ⟨⟨A', B'⟩, hAB'mem, hAB'min⟩ :=
    (activePairs m).exists_min_image (fun PQ ↦ min (ilen PQ.1) (ilen PQ.2)) ⟨(A, B), hABmem⟩
  rw [activePairs, Finset.mem_filter] at hAB'mem
  obtain ⟨-, hA'act, hB'act, hA'B'p⟩ := hAB'mem
  -- minimality, in the form ClaimA consumes
  have hmin : ∀ P Q : Fin (N + 1) × Fin (N + 1), 1 ≤ m P → 1 ≤ m Q → pairBox P Q →
      min (ilen A') (ilen B') ≤ min (ilen P) (ilen Q) := by
    intro P Q hP hQ hPQ
    have hPQmem : (P, Q) ∈ activePairs m := by
      rw [activePairs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hP, hQ, hPQ⟩
    exact hAB'min (P, Q) hPQmem
  -- a covered vertex `k` has `1 ≤ e k`, and the decremented partition lands in `kostantPartitions`
  obtain ⟨a, d'⟩ := A'
  obtain ⟨c, d⟩ := B'
  dsimp only at hA'act hB'act hA'B'p hmin
  -- the pairing relations, as ℕ-facts
  have hp1 : (a : ℕ) < c := by have := hA'B'p.1; dsimp only at this; exact_mod_cast this
  have hp2 : (c : ℕ) ≤ (d' : ℕ) + 1 := by have := hA'B'p.2.1; dsimp only at this; exact_mod_cast this
  have hp3 : (d' : ℕ) < d := by have := hA'B'p.2.2; dsimp only at this; exact_mod_cast this
  have had : (a : ℕ) ≤ d' := by omega  -- `[a,d']` is an interval (left member of a valid pair)
  have hcd_int : (c : ℕ) ≤ d := by omega
  rcases lt_or_ge (ilen (c, d)) (ilen (a, d')) with hlonger | hshorter
  · -- I = B* = [c,d] (right member, strictly shorter); split at `k = d' + 1`, partner `(a, d')` left
    set k : Fin (N + 1) := ⟨(d' : ℕ) + 1, by have := d.isLt; omega⟩ with hkdef
    have hkval : (k : ℕ) = (d' : ℕ) + 1 := by rw [hkdef]
    have hck : c ≤ k := Fin.le_def.mpr (by omega)
    have hkd : k ≤ d := Fin.le_def.mpr (by omega)
    have hek : 1 ≤ e k := by
      rw [hkost k]
      refine le_trans hB'act (Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hck, hkd⟩
    have hcorner : ((c, d) : Fin (N + 1) × Fin (N + 1)) ≠ ((0 : Fin (N + 1)), Fin.last N) := by
      rintro h; rw [h, hc0] at hB'act; exact absurd hB'act (by norm_num)
    -- shortest-covering of `k`, via ClaimA (right case)
    have hshort : ∀ Y : Fin (N + 1) × Fin (N + 1), 1 ≤ m Y →
        (Y.1 : ℤ) ≤ (d' : ℤ) + 1 → (d' : ℤ) + 1 ≤ (Y.2 : ℤ) →
        (d : ℤ) - (c : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ) :=
      fun Y hY h1 h2 ↦ claimA_right hA'act hB'act hA'B'p hlonger hmin hY h1 h2
    have hkdc : (d' : ℤ) + 1 = (k : ℤ) := by rw [hkval]; push_cast; ring
    refine ⟨k, hek, ?_⟩
    rcases lt_or_eq_of_le (Fin.le_def.mp hck) with hck' | hck'
    · rcases lt_or_eq_of_le (Fin.le_def.mp hkd) with hkd' | hkd'
      · -- interior `c < k < d`: redMove, partner `(a, d')` to the LEFT (`b = d' = k−1`)
        set b : Fin (N + 1) := ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ with hbdef
        set cc : Fin (N + 1) := ⟨(k : ℕ) + 1, by have := d.isLt; omega⟩ with hccdef
        have hbk : (k : ℕ) = (b : ℕ) + 1 := by rw [hbdef]; dsimp only; omega
        have hccval : (cc : ℕ) = (b : ℕ) + 2 := by rw [hbdef, hccdef]; dsimp only; omega
        have hcbb : (c : ℕ) ≤ b := by rw [hbdef]; dsimp only; omega
        have hccd : (cc : ℕ) ≤ d := by rw [hccdef]; dsimp only; omega
        have hbeqd' : b = d' := Fin.ext (by rw [hbdef]; dsimp only; omega)
        have hbkc : (b : ℤ) + 1 = (d' : ℤ) + 1 := by rw [hbeqd']
        have hkeq : k = (⟨(b : ℕ) + 1, by have := k.isLt; omega⟩ : Fin (N + 1)) := Fin.ext (by omega)
        refine ⟨redMove m c b cc d, ?_, ?_⟩
        · rw [hkeq]
          exact redMove_mem hm (Fin.le_def.mpr (by omega)) (Fin.le_def.mpr (by omega)) hccval hccd
            (by dsimp only [Fin.val_mk]) hB'act hcorner
        · refine codimForm_redMove_lt m hcbb hccval hccd hB'act
            (fun Y hY h1 h2 ↦ hshort Y hY (by rw [hbkc] at h1; exact h1)
              (by rw [hbkc] at h2; exact h2))
            (P := (a, b)) (by rw [hbeqd']; exact hA'act) ?_
          exact splitCoeff_partner_left_le hcbb hccval hccd hp1
      · -- right endpoint `k = d`: rightShrink, partner `(a, d')` LEFT (`b = d−1 = d'`)
        have hkeqd : k = d := Fin.ext hkd'
        have hdd' : (d : ℕ) = (d' : ℕ) + 1 := by omega
        set b : Fin (N + 1) := ⟨(d : ℕ) - 1, by have := d.isLt; omega⟩ with hbdef
        have hbd2 : (b : ℕ) + 1 = d := by rw [hbdef]; dsimp only; omega
        have hcbb : (c : ℕ) ≤ b := by rw [hbdef]; dsimp only; omega
        have hbeqd' : b = d' := Fin.ext (by rw [hbdef]; dsimp only; omega)
        have hdk : (d : ℤ) = (d' : ℤ) + 1 := by exact_mod_cast hdd'
        refine ⟨rightShrink m c b d, ?_, ?_⟩
        · rw [hkeqd]
          exact rightShrink_mem hm (Fin.le_def.mpr hcbb) hbd2 (Fin.le_def.mpr hcd_int) hB'act hcorner
        · refine codimForm_rightShrink_lt m hcbb hbd2 hB'act
            (fun Y hY h1 h2 ↦ hshort Y hY (by rw [hdk] at h1; exact h1)
              (by rw [hdk] at h2; exact h2))
            (P := (a, b)) (by rw [hbeqd']; exact hA'act) ?_
          exact rightCoeff_partner_le hcbb hbd2 hp1
    · -- left endpoint `k = c`: leftShrink, partner `(a, d')` LEFT (`d' = c−1`)
      have hkeqc : k = c := Fin.ext hck'.symm
      have hcc1 : (c : ℕ) = (d' : ℕ) + 1 := by omega
      rcases lt_or_eq_of_le (Fin.le_def.mp hkd) with hkd' | hkd'
      · -- `k = c < d`: leftShrink, partner `(a, d')` left (`d' = c−1`)
        set cc : Fin (N + 1) := ⟨(c : ℕ) + 1, by have := d.isLt; omega⟩ with hccdef
        have hccval : (cc : ℕ) = (c : ℕ) + 1 := by rw [hccdef]
        have hccd : (cc : ℕ) ≤ d := by rw [hccdef]; omega
        have hd'eq : (d' : ℤ) + 1 = (c : ℤ) := by
          have : (c : ℤ) = (d' : ℤ) + 1 := by exact_mod_cast hcc1
          omega
        set b' : Fin (N + 1) := ⟨(c : ℕ) - 1, by have := c.isLt; omega⟩ with hb'def
        have hb'eqd' : b' = d' := Fin.ext (by rw [hb'def]; dsimp only; omega)
        have hb'a : (b' : ℕ) + 1 = c := by rw [hb'def]; dsimp only; omega
        refine ⟨leftShrink m c cc d, ?_, ?_⟩
        · rw [hkeqc]
          exact leftShrink_mem hm hccval hccd (Fin.le_def.mpr hcd_int) hB'act hcorner
        · refine codimForm_leftShrink_lt m hccval hccd hB'act
            (fun Y hY h1 h2 ↦ hshort Y hY (by rw [← hd'eq] at h1; exact h1)
              (by rw [← hd'eq] at h2; exact h2))
            (P := (a, b')) (by rw [hb'eqd']; exact hA'act) ?_
          exact leftCoeff_partner_left_le hccval hccd hb'a hp1
      · -- singleton `k = c = d`: removeMove, partner `(a, d')` right-form (`d' = c−1`)
        have hkeqd : k = d := Fin.ext hkd'
        have hceqdN : (c : ℕ) = (d : ℕ) := by rw [← hkeqc, hkeqd]
        have hd'1 : (d' : ℕ) + 1 = c := by omega
        have hsac : 1 ≤ m (c, c) := by
          have hceqd : c = d := Fin.ext hceqdN
          rw [← hceqd] at hB'act; exact hB'act
        have hPc : removeCoeff c (a, d') ≤ -1 :=
          removeCoeff_partner_right_le (a := c) (b := d') (A1 := a) hd'1 (by exact_mod_cast hp1)
        rw [hkeqc]
        exact ⟨removeMove m c, removeMove_mem hm hsac, codimForm_removeMove_lt m hsac hA'act hPc⟩
  · -- I = A* = [a,d'] (left member); split at `k = c − 1`
    -- `k` as a `Fin`, `k = c − 1`, covered by `[a,d']`
    have hcpos : 1 ≤ (c : ℕ) := by omega
    set k : Fin (N + 1) := ⟨(c : ℕ) - 1, by have := c.isLt; omega⟩ with hkdef
    have hkval : (k : ℕ) = (c : ℕ) - 1 := by rw [hkdef]
    have hak : a ≤ k := Fin.le_def.mpr (by omega)
    have hkd : k ≤ d' := Fin.le_def.mpr (by omega)
    have hek : 1 ≤ e k := by
      rw [hkost k]
      refine le_trans hA'act (Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hak, hkd⟩
    have hcorner : ((a, d') : Fin (N + 1) × Fin (N + 1)) ≠ ((0 : Fin (N + 1)), Fin.last N) := by
      rintro h; rw [h, hc0] at hA'act; exact absurd hA'act (by norm_num)
    -- shortest-covering of `k`, via ClaimA (left case)
    have hshort : ∀ Y : Fin (N + 1) × Fin (N + 1), 1 ≤ m Y →
        (Y.1 : ℤ) ≤ (c : ℤ) - 1 → (c : ℤ) - 1 ≤ (Y.2 : ℤ) →
        (d' : ℤ) - (a : ℤ) ≤ (Y.2 : ℤ) - (Y.1 : ℤ) :=
      fun Y hY h1 h2 ↦ claimA_left hA'act hB'act hA'B'p hshorter hmin hY h1 h2
    have hkc : (c : ℤ) - 1 = (k : ℤ) := by rw [hkval]; omega
    -- ClaimA in the `(b:ℤ)+1`/`d'`/`a` covering forms each move's `hshort` expects
    refine ⟨k, hek, ?_⟩
    rcases lt_or_eq_of_le (Fin.le_def.mp hak) with hak' | hak'
    · rcases lt_or_eq_of_le (Fin.le_def.mp hkd) with hkd' | hkd'
      · -- interior `a < k < d'`: redMove, partner `(c, d)` (`c = k+1`)
        set b : Fin (N + 1) := ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ with hbdef
        set cc : Fin (N + 1) := ⟨(k : ℕ) + 1, by have := d'.isLt; omega⟩ with hccdef
        have hbk : (k : ℕ) = (b : ℕ) + 1 := by rw [hbdef]; dsimp only; omega
        have hccval : (cc : ℕ) = (b : ℕ) + 2 := by rw [hbdef, hccdef]; dsimp only; omega
        have habb : (a : ℕ) ≤ b := by rw [hbdef]; dsimp only; omega
        have hccd : (cc : ℕ) ≤ d' := by rw [hccdef]; dsimp only; omega
        have hcceqc : cc = c := Fin.ext (by rw [hccdef]; dsimp only; omega)
        have hccc : (c : ℕ) = (b : ℕ) + 2 := by rw [← hcceqc]; exact hccval
        have hbkc : (b : ℤ) + 1 = (c : ℤ) - 1 := by
          have hcz : (c : ℤ) = (b : ℤ) + 2 := by exact_mod_cast hccc
          omega
        have hkeq : k = (⟨(b : ℕ) + 1, by have := k.isLt; omega⟩ : Fin (N + 1)) := Fin.ext (by omega)
        refine ⟨redMove m a b cc d', ?_, ?_⟩
        · rw [hkeq]
          exact redMove_mem hm (Fin.le_def.mpr (by omega)) (Fin.le_def.mpr (by omega)) hccval hccd
            (by dsimp only [Fin.val_mk]) hA'act hcorner
        · refine codimForm_redMove_lt m habb hccval hccd hA'act
            (fun Y hY h1 h2 ↦ hshort Y hY (by rw [hbkc] at h1; exact h1)
              (by rw [hbkc] at h2; exact h2))
            (P := (cc, d)) (by rw [hcceqc]; exact hB'act) ?_
          exact splitCoeff_partner_le habb hccval hccd (by exact_mod_cast hp3)
      · -- right endpoint `k = d'`: rightShrink, partner `(c, d)` to the RIGHT (`c = d'+1`)
        have hkeqd : k = d' := Fin.ext hkd'
        have hcd'1 : (c : ℕ) = (d' : ℕ) + 1 := by omega
        set b : Fin (N + 1) := ⟨(d' : ℕ) - 1, by have := d'.isLt; omega⟩ with hbdef
        have hbd2 : (b : ℕ) + 1 = d' := by rw [hbdef]; dsimp only; omega
        have habb : (a : ℕ) ≤ b := by rw [hbdef]; dsimp only; omega
        have hdc : (d' : ℤ) = (c : ℤ) - 1 := by have : (c : ℤ) = (d' : ℤ) + 1 := by exact_mod_cast hcd'1
                                                omega
        refine ⟨rightShrink m a b d', ?_, ?_⟩
        · rw [hkeqd]
          exact rightShrink_mem hm (Fin.le_def.mpr habb) hbd2 (Fin.le_def.mpr had) hA'act hcorner
        · refine codimForm_rightShrink_lt m habb hbd2 hA'act
            (fun Y hY h1 h2 ↦ hshort Y hY (by rw [hdc] at h1; exact h1) (by rw [hdc] at h2; exact h2))
            (P := (c, d)) hB'act ?_
          exact rightCoeff_partner_right_le habb hbd2 (by exact_mod_cast hcd'1) (by exact_mod_cast hp3)
    · -- left endpoint `k = a`
      have hkeqa : k = a := Fin.ext hak'.symm
      have hac : (a : ℤ) = (c : ℤ) - 1 := by
        have h1 : (a : ℕ) = (c : ℕ) - 1 := by omega
        have h2 : (c : ℤ) = (a : ℤ) + 1 := by exact_mod_cast (by omega : (c : ℕ) = (a : ℕ) + 1)
        omega
      rcases lt_or_eq_of_le (Fin.le_def.mp hkd) with hkd' | hkd'
      · -- `k = a < d'`: leftShrink, partner `(c, d)` (`c = a+1`)
        have hcca : (c : ℕ) = (a : ℕ) + 1 := by omega
        set cc : Fin (N + 1) := ⟨(a : ℕ) + 1, by have := d'.isLt; omega⟩ with hccdef
        have hccval : (cc : ℕ) = (a : ℕ) + 1 := by rw [hccdef]
        have hccd : (cc : ℕ) ≤ d' := by rw [hccdef]; omega
        have hcceqc : cc = c := Fin.ext (by rw [hccdef]; omega)
        refine ⟨leftShrink m a cc d', ?_, ?_⟩
        · rw [hkeqa]
          exact leftShrink_mem hm hccval hccd (Fin.le_def.mpr had) hA'act hcorner
        · refine codimForm_leftShrink_lt m hccval hccd hA'act
            (fun Y hY h1 h2 ↦ hshort Y hY (by rw [hac] at h1; exact h1) (by rw [hac] at h2; exact h2))
            (P := (cc, d)) (by rw [hcceqc]; exact hB'act) ?_
          exact leftCoeff_partner_le hccval hccd (by exact_mod_cast hp3)
      · -- singleton `k = a = d'`: removeMove, partner `(c, d)` left-form (`c = a+1`)
        have hkeqd : k = d' := Fin.ext hkd'
        have haeqdN : (a : ℕ) = (d' : ℕ) := by rw [← hkeqa, hkeqd]
        have hcca : (c : ℕ) = (a : ℕ) + 1 := by omega
        have haN : (a : ℕ) < N := by have := d.isLt; omega
        have haltd : (a : ℕ) < d := by omega
        have haeqd : a = d' := Fin.ext haeqdN
        have hsak : 1 ≤ m (a, a) := by rw [← haeqd] at hA'act; exact hA'act
        have hPc : removeCoeff a (c, d) ≤ -1 :=
          removeCoeff_partner_left_le (a := a) (c := c) (B2 := d) hcca haN haltd
        rw [hkeqa]
        exact ⟨removeMove m a, removeMove_mem hm hsak, codimForm_removeMove_lt m hsak hB'act hPc⟩

/-- **Strict all-vertex dimension-monotonicity of `cCodim · 0`.** If `e v < e' v` at *every* vertex,
then `cCodim e 0 < cCodim e' 0`. A minimiser `m'` of `cCodim e' 0` has full coverage (every
`e' v ≥ 1`), hence `codimForm ≥ 1` (Lemma Y); `reduceStep_strict` drops it by `≥ 1` to a partition of
`e'` decremented at some `k`, which still dominates `e` (`e ≤ e''`), so the LANDED weak monotonicity
gives `cCodim e 0 ≤ cCodim e' 0 − 1 < cCodim e' 0`. -/
theorem cCodim_zero_strict {e e' : Fin (N + 1) → ℕ}
    (he : (kostantPartitions e 0).Nonempty) (he' : (kostantPartitions e' 0).Nonempty)
    (hlt : ∀ k, e k < e' k) :
    cCodim e 0 he < cCodim e' 0 he' := by
  -- `cCodim e' 0` is attained at a minimiser `m'`
  obtain ⟨m', hm'mem, hm'eq⟩ := (kostantPartitions e' 0).exists_mem_eq_inf' he'
    (fun m ↦ codimForm N (extendℤ m))
  -- `e'` is full coverage, so `codimForm (extendℤ m') ≥ 1` (Lemma Y)
  have hfull : ∀ v, 1 ≤ e' v := fun v ↦ by have := hlt v; omega
  have hpos : 1 ≤ codimForm N (extendℤ m') :=
    codimForm_extendℤ_pos_of_fullCover hm'mem hfull
  -- a strict reduction step at some vertex `k`
  obtain ⟨k, hek, m'', hm''mem, hm''le⟩ := reduceStep_strict hm'mem hpos
  -- the decremented vector still dominates `e` (since `e < e'` at every vertex)
  set e'' := Function.update e' k (e' k - 1) with he''
  have hle : ∀ v, e v ≤ e'' v := by
    intro v; rw [he'']
    by_cases hv : v = k
    · rw [hv, Function.update_self]; have := hlt k; omega
    · rw [Function.update_of_ne hv]; have := hlt v; omega
  -- LANDED weak monotonicity: a partition of `e` dominates `m''`
  obtain ⟨m, hmmem, hmle⟩ := exists_le_codimForm (∑ v, e'' v) e e'' rfl hle m'' hm''mem
  -- chain: `cCodim e ≤ codimForm m ≤ codimForm m'' ≤ codimForm m' − 1`, and `codimForm m' = cCodim e'`
  have hchain : cCodim e 0 he ≤ codimForm N (extendℤ m') - 1 := by
    calc cCodim e 0 he = (kostantPartitions e 0).inf' he (fun m ↦ codimForm N (extendℤ m)) := rfl
      _ ≤ codimForm N (extendℤ m) := Finset.inf'_le _ hmmem
      _ ≤ codimForm N (extendℤ m'') := hmle
      _ ≤ codimForm N (extendℤ m') - 1 := hm''le
  have heq : codimForm N (extendℤ m') = cCodim e' 0 he' := hm'eq.symm
  rw [heq] at hchain
  linarith

/-- **θ-count headline, UNCONDITIONAL.** `numTop d r = #{top-dimensional irreducible components of
`Σ̄^r`}`. Both gating monotonicities of `Core.CCodimCornerMono` are now discharged: the weak one by
`Core.CCodimZeroMono.cCodim_zero_mono`, the strict all-vertex one by `cCodim_zero_strict`. -/
theorem numTop_eq_ncard_topComponents {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : (kostantPartitions d r).Nonempty) :
    numTop d r hr = (topComponents (k := k) d r hr).ncard :=
  numTop_eq_ncard_topComponents_of_strict
    (fun he he' hlt ↦ cCodim_zero_strict he he' hlt) d r hr

end DLNFibre.Core
