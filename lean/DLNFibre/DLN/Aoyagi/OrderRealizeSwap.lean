import DLNFibre.DLN.Aoyagi.OrderRealize

/-!
# `DLN.Aoyagi.OrderRealizeSwap` — the one-swap order-iso (P6.2 Tier-3, obligation (a)+(b))

Delivers `swapBinding_orderIso_impl`, the coupled one adjacent-width-swap order-isomorphism
`bindingSet M ≃o bindingSet (swapWidths k M)` (seat-Eswap). This discharges the sorried
`swapBinding_orderIso` in `OrderRealize.lean` (seat-E wires the discharge; kept in a separate module
to avoid an import cycle, since `OrderRealize` owns the floor defs/lemmas this reuses).

The transport is `swapProfile M k` (Codex's value-preserving `swapR` on the coupled coordinate
`k−1`). The construction reuses the floor lemmas `swapR_swapR` (involution),
`swapWidths_swapWidths`, `swapR_F_invariant` (value-preservation heart).

**Decomposition of the obligation (numerically de-risked, threads/41-order-count/swap-*.py):**
* PURE arithmetic (no profiles): `swapR_ge_Q`/`swapR_le_P` (range, omega); `swapR_le_B_of_min` and
  `swapR_mono_of_min` — the two facts that genuinely need the *minimiser* hypothesis (atomic
  `swapR`-in-`X` monotonicity is FALSE off binding profiles). Both are pure `swapR` + minimiser
  facts (verified 0-fail over all coord-ordered minimiser pairs incl. all tie sub-cases).
* `mvTerm` / `Mval_diff_offdiag` — the `Mval` sum splits into the two terms `{k−1, k}` that read the
  swapped coordinate; all others cancel.
* Profile side: `bindingSet_local_min` extracts the minimiser hypothesis; `swapProfile_Mval_eq`
  (value-preservation), `swapProfile_mem_Adm`, `swapProfile_swapProfile` (involution),
  `minAdm_swapWidths_eq`, `swapProfile_mem_bindingSet`, `swapProfile_mono`.
-/

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Pure `swapR` + minimiser arithmetic (no profiles) -/

/-- The two `Mval` terms that read the swapped coordinate, as a function of that coordinate `X`:
`F_{A,B}(P,X,Q) = (P−X)(A−X) + (X−Q)(B−Q)` over `ℤ`. -/
def swapFℤ (P X Q A B : ℕ) : ℤ :=
  ((P : ℤ) - X) * ((A : ℤ) - X) + ((X : ℤ) - Q) * ((B : ℤ) - Q)

/-- `swapR` never drops below `Q` on the admissible range. -/
theorem swapR_ge_Q {P X Q A B : ℕ} (hQX : Q ≤ X) (hXP : X ≤ P) :
    Q ≤ swapR P X Q A B := by
  unfold swapR
  split_ifs with h1 h2 <;> omega

/-- `swapR` never rises above `P` on the admissible range. -/
theorem swapR_le_P {P X Q A B : ℕ} (hQX : Q ≤ X) (hXP : X ≤ P) :
    swapR P X Q A B ≤ P := by
  unfold swapR
  split_ifs with h1 h2 <;> omega

/-- **Adm-preservation crux**: on a binding profile (`X` minimises `swapFℤ` over `[Q, min(P,A)]`),
the swap image stays within the swapped upper bound `B`. Needed only in the reflection branch with
`B < A` (there `X = P`, forced by the single neighbour inequality `F(X) ≤ F(X+1)`). -/
theorem swapR_le_B_of_min {P X Q A B : ℕ} (hQX : Q ≤ X) (hXP : X ≤ P) (hXA : X ≤ A)
    (hQA : Q ≤ A) (hQB : Q ≤ B)
    (hmin : ∀ Y : ℕ, Q ≤ Y → Y ≤ P → Y ≤ A → swapFℤ P X Q A B ≤ swapFℤ P Y Q A B) :
    swapR P X Q A B ≤ B := by
  unfold swapR
  split_ifs with h1 h2
  · -- translation up: `X + (B - A) ≤ B` from `X ≤ A`
    obtain ⟨h1a, h1b⟩ := h1; omega
  · -- translation down: `X - (A - B) ≤ B` from `X ≤ A`
    obtain ⟨h2a, h2b⟩ := h2; omega
  · -- reflection `P + Q - X ≤ B`
    rw [not_and_or] at h1 h2
    by_cases hAB : A ≤ B
    · -- `A ≤ B`: no minimality needed (`Q ≤ A` closes it)
      omega
    · -- `B < A`: minimality forces `X = P` (then `P + Q - X = Q ≤ B`)
      by_cases hXeqP : X = P
      · omega
      · have hXltA : X < A := by omega
        have hstep := hmin (X + 1) (by omega) (by omega) (by omega)
        have hdiff : swapFℤ P (X + 1) Q A B - swapFℤ P X Q A B
            = 2 * (X : ℤ) - P - A + 1 + B - Q := by
          unfold swapFℤ; push_cast; ring
        omega

/-- **Coupled monotonicity** (the load-bearing hazard): if `(P,X,Q) ≤ (P',X',Q')` coordinatewise and
both `X`, `X'` are minimisers of their respective `swapFℤ` over their admissible ranges (same widths
`A, B`), then `swapR` is monotone. Atomic `swapR`-in-`X` monotonicity is FALSE; the minimiser
hypotheses are load-bearing. -/
theorem swapR_mono_of_min {P X Q A B P' X' Q' : ℕ}
    (hQX : Q ≤ X) (hXP : X ≤ P) (hXA : X ≤ A) (hQA : Q ≤ A) (hQB : Q ≤ B)
    (hQX' : Q' ≤ X') (hXP' : X' ≤ P') (hXA' : X' ≤ A) (hQA' : Q' ≤ A) (hQB' : Q' ≤ B)
    (hPP : P ≤ P') (hXX : X ≤ X') (hQQ : Q ≤ Q')
    (hmin : ∀ Y : ℕ, Q ≤ Y → Y ≤ P → Y ≤ A → swapFℤ P X Q A B ≤ swapFℤ P Y Q A B)
    (hmin' : ∀ Y : ℕ, Q' ≤ Y → Y ≤ P' → Y ≤ A → swapFℤ P' X' Q' A B ≤ swapFℤ P' Y Q' A B) :
    swapR P X Q A B ≤ swapR P' X' Q' A B := by
  by_cases hAB : A ≤ B
  · -- regime `A ≤ B`: a reflected primed minimiser collapses to `X' = Q'` (output `P'`)
    have hcol' : (B - A ≤ P' - X') ∨ X' = Q' := by
      by_cases hc : B - A ≤ P' - X'
      · exact Or.inl hc
      · refine Or.inr ?_
        by_contra hne
        have hgt : Q' < X' := lt_of_le_of_ne hQX' (Ne.symm hne)
        have hstep := hmin' (X' - 1) (by omega) (by omega) (by omega)
        have hcast : ((X' - 1 : ℕ) : ℤ) = (X' : ℤ) - 1 := by omega
        have hdiff : swapFℤ P' (X' - 1) Q' A B - swapFℤ P' X' Q' A B
            = (P' : ℤ) + A + Q' - B + 1 - 2 * X' := by
          unfold swapFℤ; simp only [hcast]; ring
        omega
    unfold swapR
    split_ifs <;> omega
  · -- regime `B < A`: a reflected unprimed minimiser collapses to `X = P` (output `Q`)
    push_neg at hAB
    have hcol : (A - B ≤ X - Q) ∨ X = P := by
      by_cases hc : A - B ≤ X - Q
      · exact Or.inl hc
      · refine Or.inr ?_
        by_contra hne
        have hlt : X < P := lt_of_le_of_ne hXP hne
        have hXltA : X < A := by omega
        have hstep := hmin (X + 1) (by omega) (by omega) (by omega)
        have hdiff : swapFℤ P (X + 1) Q A B - swapFℤ P X Q A B
            = 2 * (X : ℤ) - P - A + 1 + B - Q := by
          unfold swapFℤ; push_cast; ring
        omega
    unfold swapR
    split_ifs <;> omega

/-! ## `Mval` two-term decomposition -/

/-- A single `Mval` summand: `(t⁽ʲ⁻¹⁾ − t⁽ʲ⁾)(M⁽ʲ⁺¹⁾ − t⁽ʲ⁾)`. `Mval M T = ∑ j, mvTerm M T j`. -/
def mvTerm (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) : ℤ :=
  (tPrev M T j - (T j : ℤ)) * ((M j.succ : ℤ) - (T j : ℤ))

/-- `Mval` is the sum of its terms (definitional). -/
theorem Mval_eq_sum_mvTerm (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) :
    Mval M T = ∑ j, mvTerm M T j := rfl

/-- Only the two terms `{k−1, k}` read the swapped coordinate; if all others agree, the `Mval`
difference is the difference of those two terms. -/
theorem Mval_diff_offdiag (M₁ M₂ : Fin (L + 1) → ℕ) (T₁ T₂ : Fin L → ℕ) (k : Fin L)
    (hk : 0 < k.val) (hlt : k.val - 1 < L)
    (hoff : ∀ j : Fin L, j ≠ ⟨k.val - 1, hlt⟩ → j ≠ k → mvTerm M₂ T₂ j = mvTerm M₁ T₁ j) :
    Mval M₂ T₂ - Mval M₁ T₁
      = (mvTerm M₂ T₂ ⟨k.val - 1, hlt⟩ - mvTerm M₁ T₁ ⟨k.val - 1, hlt⟩)
        + (mvTerm M₂ T₂ k - mvTerm M₁ T₁ k) := by
  have hne : (⟨k.val - 1, hlt⟩ : Fin L) ≠ k := by
    rw [ne_eq, Fin.ext_iff]; show ¬ k.val - 1 = k.val; omega
  have hfzero : ∀ x ∈ (Finset.univ : Finset (Fin L)), x ∉ ({⟨k.val - 1, hlt⟩, k} : Finset (Fin L)) →
      mvTerm M₂ T₂ x - mvTerm M₁ T₁ x = 0 := by
    intro j _ hj
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    rw [hoff j hj.1 hj.2]; ring
  rw [Mval_eq_sum_mvTerm, Mval_eq_sum_mvTerm, ← Finset.sum_sub_distrib,
    ← Finset.sum_subset (Finset.subset_univ _) hfzero, Finset.sum_pair hne]

/-! ## Index/width helpers for the swap -/

/-- `swapWidths` sends the left width vertex to the right width. -/
theorem swapWidths_castSucc (M : Fin (L + 1) → ℕ) (k : Fin L) :
    swapWidths k M k.castSucc = M k.succ := by
  simp only [swapWidths, Function.comp_apply, Equiv.swap_apply_left]

/-- `swapWidths` sends the right width vertex to the left width. -/
theorem swapWidths_succ (M : Fin (L + 1) → ℕ) (k : Fin L) :
    swapWidths k M k.succ = M k.castSucc := by
  simp only [swapWidths, Function.comp_apply, Equiv.swap_apply_right]

/-- `swapWidths` fixes any vertex distinct from the swapped pair. -/
theorem swapWidths_apply_ne (M : Fin (L + 1) → ℕ) (k : Fin L) {j : Fin (L + 1)}
    (h1 : j ≠ k.castSucc) (h2 : j ≠ k.succ) : swapWidths k M j = M j := by
  simp only [swapWidths, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- `(k-1).succ = k.castSucc` as `Fin (L+1)`, for `k ≥ 1`. -/
theorem kpred_succ_eq (k : Fin L) (hk : 0 < k.val) (hlt : k.val - 1 < L) :
    (⟨k.val - 1, hlt⟩ : Fin L).succ = k.castSucc := by
  rw [Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc]; show (k.val - 1) + 1 = k.val; omega

/-- For `k = 1`, `k.castSucc = 1` in `Fin (L+1)`. -/
theorem castSucc_eq_one (k : Fin L) (hk1 : k.val = 1) : k.castSucc = (1 : Fin (L + 1)) := by
  rw [Fin.ext_iff, Fin.coe_castSucc, hk1, Fin.val_one', Nat.mod_eq_of_lt (by have := k.isLt; omega)]

/-- For `k = 1`, `M k.castSucc = M 1` (the second width, as it appears in `admBound M 0`). -/
theorem M_castSucc_eq_one (M : Fin (L + 1) → ℕ) (k : Fin L) (hk1 : k.val = 1) :
    M k.castSucc = M 1 := by rw [castSucc_eq_one k hk1]

/-- `0 ≠ k.castSucc` for `k ≥ 1`. -/
theorem zero_ne_castSucc {k : Fin L} (hk : 0 < k.val) : (0 : Fin (L + 1)) ≠ k.castSucc := by
  rw [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.coe_castSucc]; omega

/-- `0 ≠ k.succ`. -/
theorem zero_ne_succ (k : Fin L) : (0 : Fin (L + 1)) ≠ k.succ := by
  rw [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ]; omega

/-- `1 ≠ k.castSucc` for `k ≥ 2`. -/
theorem one_ne_castSucc {k : Fin L} (hk2 : 2 ≤ k.val) : (1 : Fin (L + 1)) ≠ k.castSucc := by
  rw [ne_eq, Fin.ext_iff, Fin.val_one', Fin.coe_castSucc, Nat.mod_eq_of_lt (by have := k.isLt; omega)]
  omega

/-- `1 ≠ k.succ` for `k ≥ 2`. -/
theorem one_ne_succ {k : Fin L} (hk2 : 2 ≤ k.val) : (1 : Fin (L + 1)) ≠ k.succ := by
  rw [ne_eq, Fin.ext_iff, Fin.val_one', Fin.val_succ, Nat.mod_eq_of_lt (by have := k.isLt; omega)]
  omega

/-- `j.succ ≠ k.castSucc` when `j ≠ k−1`. -/
theorem succ_ne_castSucc {j k : Fin L} (hlt : k.val - 1 < L) (hk : 0 < k.val)
    (hjkp : j ≠ ⟨k.val - 1, hlt⟩) : j.succ ≠ k.castSucc := by
  rw [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc]
  intro h; exact hjkp (Fin.ext (show j.val = k.val - 1 by omega))

/-- `j.succ ≠ k.succ` when `j ≠ k`. -/
theorem succ_ne_succ_of_ne {j k : Fin L} (hjk : j ≠ k) : j.succ ≠ k.succ := by
  rw [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_succ]
  intro h; exact hjk (Fin.ext (by omega))

/-- `swapProfile` in `Function.update` form (`k ≥ 1`). -/
theorem swapProfile_eq_update (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) (T : Fin L → ℕ)
    (hlt : k.val - 1 < L) :
    swapProfile M k T = Function.update T ⟨k.val - 1, hlt⟩
      (swapR (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) (T ⟨k.val - 1, hlt⟩) (T k)
        (M k.castSucc) (M k.succ)) := by
  unfold swapProfile
  rw [dif_pos hk]

/-! ## Profile-side lemmas (`k ≥ 1`) -/

/-- Range facts on the swapped coordinate, read off `admPred`. -/
theorem swap_param_range (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) {T : Fin L → ℕ}
    (hT : T ∈ Adm M) :
    T k ≤ T ⟨k.val - 1, by omega⟩ ∧
    T ⟨k.val - 1, by omega⟩ ≤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) ∧
    T ⟨k.val - 1, by omega⟩ ≤ M k.castSucc ∧
    T k ≤ M k.castSucc ∧ T k ≤ M k.succ := by
  have hlt : k.val - 1 < L := by omega
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨-, hbound, hdec, -⟩ := hT
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hdec ⟨k.val - 1, hlt⟩ k (by rw [Fin.le_def]; show k.val - 1 ≤ k.val; omega)
  · by_cases hk1 : k.val = 1
    · rw [if_pos hk1]
      have hb := hbound ⟨k.val - 1, hlt⟩
      unfold admBound at hb
      rw [if_pos (show (⟨k.val - 1, hlt⟩ : Fin L).val = 0 by show k.val - 1 = 0; omega)] at hb
      exact le_trans hb (min_le_left _ _)
    · rw [if_neg hk1]
      exact hdec ⟨k.val - 2, by omega⟩ ⟨k.val - 1, hlt⟩
        (by rw [Fin.le_def]; show k.val - 2 ≤ k.val - 1; omega)
  · calc T ⟨k.val - 1, hlt⟩ ≤ admBound M ⟨k.val - 1, hlt⟩ := hbound _
      _ ≤ M (⟨k.val - 1, hlt⟩ : Fin L).succ := admBound_le_Msucc M _
      _ = M k.castSucc := by rw [kpred_succ_eq k hk hlt]
  · calc T k ≤ T ⟨k.val - 1, hlt⟩ :=
        hdec ⟨k.val - 1, hlt⟩ k (by rw [Fin.le_def]; show k.val - 1 ≤ k.val; omega)
      _ ≤ admBound M ⟨k.val - 1, hlt⟩ := hbound _
      _ ≤ M (⟨k.val - 1, hlt⟩ : Fin L).succ := admBound_le_Msucc M _
      _ = M k.castSucc := by rw [kpred_succ_eq k hk hlt]
  · have hb := hbound k
    unfold admBound at hb
    rw [if_neg (show ¬ k.val = 0 by omega)] at hb
    exact hb

/-- `tPrev` at a positive index reads the predecessor coordinate. -/
theorem tPrev_pos (M : Fin (L + 1) → ℕ) (f : Fin L → ℕ) (j : Fin L) (hj : 0 < j.val)
    (hlt : j.val - 1 < L) : tPrev M f j = (f ⟨j.val - 1, hlt⟩ : ℤ) := by
  unfold tPrev
  split
  · exact absurd ‹j.val = 0› (by omega)
  · rfl

/-- The two `Mval` terms reading the swapped coordinate `k−1`, for a profile updated there to `v`,
sum to `swapFℤ P v Q A B`. Shared by value-preservation and local minimality. -/
theorem mvPair_update (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) (T : Fin L → ℕ) (v : ℕ)
    (hlt : k.val - 1 < L) :
    mvTerm M (Function.update T ⟨k.val - 1, hlt⟩ v) ⟨k.val - 1, hlt⟩
      + mvTerm M (Function.update T ⟨k.val - 1, hlt⟩ v) k
      = swapFℤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) v (T k)
          (M k.castSucc) (M k.succ) := by
  have hkpk : (⟨k.val - 1, hlt⟩ : Fin L) ≠ k := by
    rw [ne_eq, Fin.ext_iff]; show ¬ k.val - 1 = k.val; omega
  have vkp : (Function.update T ⟨k.val - 1, hlt⟩ v) ⟨k.val - 1, hlt⟩ = v := by
    rw [Function.update_apply, if_pos rfl]
  have vk : (Function.update T ⟨k.val - 1, hlt⟩ v) k = T k := by
    rw [Function.update_apply, if_neg (fun h => hkpk h.symm)]
  have hMkp : M (⟨k.val - 1, hlt⟩ : Fin L).succ = M k.castSucc := by rw [kpred_succ_eq k hk hlt]
  have htk : tPrev M (Function.update T ⟨k.val - 1, hlt⟩ v) k = (v : ℤ) := by
    rw [tPrev_pos M _ k hk hlt, vkp]
  have htkp : tPrev M (Function.update T ⟨k.val - 1, hlt⟩ v) ⟨k.val - 1, hlt⟩
      = ((if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩ : ℕ) : ℤ) := by
    by_cases hk1 : k.val = 1
    · unfold tPrev
      rw [if_pos (show (⟨k.val - 1, hlt⟩ : Fin L).val = 0 by show k.val - 1 = 0; omega), if_pos hk1]
    · have hkppos : 0 < (⟨k.val - 1, hlt⟩ : Fin L).val := by show 0 < k.val - 1; omega
      have hkplt : (⟨k.val - 1, hlt⟩ : Fin L).val - 1 < L := by show k.val - 1 - 1 < L; omega
      rw [tPrev_pos M _ ⟨k.val - 1, hlt⟩ hkppos hkplt, if_neg hk1]
      congr 1
      have hidx : (⟨(⟨k.val - 1, hlt⟩ : Fin L).val - 1, hkplt⟩ : Fin L) = ⟨k.val - 2, by omega⟩ := by
        rw [Fin.mk.injEq]; show (k.val - 1) - 1 = k.val - 2; omega
      rw [hidx, Function.update_apply,
        if_neg (show (⟨k.val - 2, by omega⟩ : Fin L) ≠ ⟨k.val - 1, hlt⟩ by
          rw [ne_eq, Fin.mk.injEq]; show ¬ k.val - 2 = k.val - 1; omega)]
  unfold mvTerm swapFℤ
  rw [htkp, htk, vkp, vk, hMkp]

/-- **Value preservation**: the swap transport preserves `Mval` (reuses `swapR_F_invariant`). -/
theorem swapProfile_Mval_eq (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) {T : Fin L → ℕ}
    (hT : T ∈ Adm M) :
    Mval (swapWidths k M) (swapProfile M k T) = Mval M T := by
  have hlt : k.val - 1 < L := by omega
  obtain ⟨hQX, hXP, hXA, hQA, hQB⟩ := swap_param_range M k hk hT
  -- off-diagonal terms agree
  have hoff : ∀ j : Fin L, j ≠ ⟨k.val - 1, hlt⟩ → j ≠ k →
      mvTerm (swapWidths k M) (swapProfile M k T) j = mvTerm M T j := by
    intro j hjkp hjk
    have hjkpv : j.val ≠ k.val - 1 := fun h => hjkp (Fin.ext h)
    have hjkv : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    have hTj : swapProfile M k T j = T j := by
      rw [swapProfile_eq_update M k hk T hlt, Function.update_apply, if_neg hjkp]
    have hMsucc : (swapWidths k M) j.succ = M j.succ := by
      apply swapWidths_apply_ne
      · rw [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc]; omega
      · rw [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_succ]; omega
    have htp : tPrev (swapWidths k M) (swapProfile M k T) j = tPrev M T j := by
      unfold tPrev
      by_cases hj0 : j.val = 0
      · rw [if_pos hj0, if_pos hj0]
        congr 1
        apply swapWidths_apply_ne
        · rw [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.coe_castSucc]; omega
        · rw [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ]; omega
      · rw [if_neg hj0, if_neg hj0]
        congr 1
        rw [swapProfile_eq_update M k hk T hlt, Function.update_apply,
          if_neg (show (⟨j.val - 1, by omega⟩ : Fin L) ≠ ⟨k.val - 1, hlt⟩ by
            rw [ne_eq, Fin.mk.injEq]; omega)]
    unfold mvTerm
    rw [hTj, hMsucc, htp]
  have hdiff := Mval_diff_offdiag M (swapWidths k M) T (swapProfile M k T) k hk hlt hoff
  -- the M-side pair and the M'-side pair
  have hMpairX : mvTerm M T ⟨k.val - 1, hlt⟩ + mvTerm M T k
      = swapFℤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) (T ⟨k.val - 1, hlt⟩) (T k)
          (M k.castSucc) (M k.succ) := by
    have h := mvPair_update M k hk T (T ⟨k.val - 1, hlt⟩) hlt
    rwa [Function.update_eq_self] at h
  have hM'pair : mvTerm (swapWidths k M) (swapProfile M k T) ⟨k.val - 1, hlt⟩
      + mvTerm (swapWidths k M) (swapProfile M k T) k
      = swapFℤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩)
          (swapR (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) (T ⟨k.val - 1, hlt⟩) (T k)
            (M k.castSucc) (M k.succ)) (T k) (M k.succ) (M k.castSucc) := by
    have h := mvPair_update (swapWidths k M) k hk T
      (swapR (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) (T ⟨k.val - 1, hlt⟩) (T k)
        (M k.castSucc) (M k.succ)) hlt
    rw [swapWidths_castSucc, swapWidths_succ,
      swapWidths_apply_ne M k (show (0 : Fin (L + 1)) ≠ k.castSucc by
        rw [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.coe_castSucc]; omega)
        (show (0 : Fin (L + 1)) ≠ k.succ by rw [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ]; omega),
      ← swapProfile_eq_update M k hk T hlt] at h
    exact h
  have hinv : swapFℤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) (T ⟨k.val - 1, hlt⟩) (T k)
        (M k.castSucc) (M k.succ)
      = swapFℤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩)
          (swapR (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) (T ⟨k.val - 1, hlt⟩) (T k)
            (M k.castSucc) (M k.succ)) (T k) (M k.succ) (M k.castSucc) := by
    unfold swapFℤ
    exact swapR_F_invariant _ (T ⟨k.val - 1, hlt⟩) (T k) (M k.castSucc) (M k.succ) hQX hXP
  linarith [hdiff, hMpairX, hM'pair, hinv]

/-- Membership of an updated profile in `Adm M`: `decrease`/`last`/`piFinset` from the base facts,
plus a supplied per-coordinate bound. Generic in the width vector (the base need not lie in `Adm M`;
only its decrease/last are used). -/
theorem update_mem_Adm (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) {T : Fin L → ℕ} (v : ℕ)
    (hlt : k.val - 1 < L)
    (hdec : ∀ i j : Fin L, i ≤ j → T j ≤ T i) (hlast : ∀ j : Fin L, j.val = L - 1 → T j = 0)
    (hbound : ∀ j : Fin L, (Function.update T ⟨k.val - 1, hlt⟩ v) j ≤ admBound M j)
    (hQv : T k ≤ v) (hvP : k.val ≠ 1 → v ≤ T ⟨k.val - 2, by omega⟩) :
    Function.update T ⟨k.val - 1, hlt⟩ v ∈ Adm M := by
  rw [Adm, Finset.mem_filter]
  refine ⟨?_, hbound, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]; intro j; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (hbound j)
  · intro i j hij
    by_cases hikp : i = ⟨k.val - 1, hlt⟩ <;> by_cases hjkp : j = ⟨k.val - 1, hlt⟩
    · subst hikp; subst hjkp; simp
    · subst hikp
      rw [Function.update_self, Function.update_of_ne hjkp]
      have hjv : j.val ≠ k.val - 1 := fun h => hjkp (Fin.ext h)
      have hijv : k.val - 1 ≤ j.val := Fin.le_def.mp hij
      exact le_trans (hdec k j (Fin.le_def.mpr (by omega))) hQv
    · subst hjkp
      rw [Function.update_self, Function.update_of_ne hikp]
      have hiv2 : i.val ≤ k.val - 1 := Fin.le_def.mp hij
      have hikv : i.val ≠ k.val - 1 := fun h => hikp (Fin.ext h)
      have hk1 : k.val ≠ 1 := by omega
      exact le_trans (hvP hk1)
        (hdec i ⟨k.val - 2, by omega⟩ (Fin.le_def.mpr (show i.val ≤ k.val - 2 by omega)))
    · rw [Function.update_of_ne hjkp, Function.update_of_ne hikp]; exact hdec i j hij
  · intro j hjlast
    have hjne : j ≠ ⟨k.val - 1, hlt⟩ := by
      rw [ne_eq, Fin.ext_iff]; show ¬ j.val = k.val - 1; have := k.isLt; omega
    rw [Function.update_of_ne hjne]; exact hlast j hjlast

/-- The perturbed profile (update `k−1` to `v` with `Q ≤ v ≤ P`, `v ≤ A`) stays admissible on `M`. -/
theorem update_kp_mem_Adm (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) {T : Fin L → ℕ}
    (hT : T ∈ Adm M) (v : ℕ) (hlt : k.val - 1 < L)
    (hQv : T k ≤ v) (hvP : v ≤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩))
    (hvA : v ≤ M k.castSucc) :
    Function.update T ⟨k.val - 1, hlt⟩ v ∈ Adm M := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨-, hbT, hdec, hlast⟩ := hT
  refine update_mem_Adm M k hk v hlt hdec hlast ?_ hQv ?_
  · intro j
    by_cases hjkp : j = ⟨k.val - 1, hlt⟩
    · subst hjkp
      rw [Function.update_self]
      by_cases hk1 : k.val = 1
      · unfold admBound
        rw [if_pos (show (⟨k.val - 1, hlt⟩ : Fin L).val = 0 by show k.val - 1 = 0; omega)]
        refine le_min ?_ ?_
        · rw [if_pos hk1] at hvP; exact hvP
        · rw [M_castSucc_eq_one M k hk1] at hvA; exact hvA
      · unfold admBound
        rw [if_neg (show ¬ (⟨k.val - 1, hlt⟩ : Fin L).val = 0 by show ¬ k.val - 1 = 0; omega),
          kpred_succ_eq k hk hlt]
        exact hvA
    · rw [Function.update_of_ne hjkp]; exact hbT j
  · intro hk1; rw [if_neg hk1] at hvP; exact hvP

/-- **Local minimality**: on a binding profile, the swapped coordinate `X = T k−1` minimises
`swapFℤ P · Q A B` over its admissible range `[Q, min(P,A)]` (perturbing only `k−1` stays admissible
and shifts `Mval` by the `swapFℤ`-difference). -/
theorem bindingSet_local_min (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) {T : Fin L → ℕ}
    (hT : T ∈ bindingSet M) :
    ∀ Y : ℕ, T k ≤ Y → Y ≤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) → Y ≤ M k.castSucc →
      swapFℤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) (T ⟨k.val - 1, by omega⟩) (T k)
          (M k.castSucc) (M k.succ)
        ≤ swapFℤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) Y (T k) (M k.castSucc)
          (M k.succ) := by
  intro Y hQY hYP hYA
  have hlt : k.val - 1 < L := by omega
  obtain ⟨hTadm, hTval⟩ := hT
  have hadm : Function.update T ⟨k.val - 1, hlt⟩ Y ∈ Adm M :=
    update_kp_mem_Adm M k hk hTadm Y hlt hQY hYP hYA
  have hoff : ∀ j : Fin L, j ≠ ⟨k.val - 1, hlt⟩ → j ≠ k →
      mvTerm M (Function.update T ⟨k.val - 1, hlt⟩ Y) j = mvTerm M T j := by
    intro j hjkp hjk
    unfold mvTerm
    rw [Function.update_of_ne hjkp]
    congr 1
    unfold tPrev
    by_cases hj0 : j.val = 0
    · rw [if_pos hj0, if_pos hj0]
    · rw [if_neg hj0, if_neg hj0]
      congr 1
      rw [Function.update_of_ne (show (⟨j.val - 1, by omega⟩ : Fin L) ≠ ⟨k.val - 1, hlt⟩ by
        rw [ne_eq, Fin.mk.injEq]
        intro h; exact hjk (Fin.ext (by omega)))]
  have hdiff := Mval_diff_offdiag M M T (Function.update T ⟨k.val - 1, hlt⟩ Y) k hk hlt hoff
  have hpairY := mvPair_update M k hk T Y hlt
  have hpairX : mvTerm M T ⟨k.val - 1, hlt⟩ + mvTerm M T k
      = swapFℤ (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) (T ⟨k.val - 1, hlt⟩) (T k)
          (M k.castSucc) (M k.succ) := by
    have h := mvPair_update M k hk T (T ⟨k.val - 1, hlt⟩) hlt
    rwa [Function.update_eq_self] at h
  have hle : Mval M T ≤ Mval M (Function.update T ⟨k.val - 1, hlt⟩ Y) := by
    rw [hTval]; exact Finset.inf'_le _ hadm
  linarith [hdiff, hpairY, hpairX, hle]

/-- **Admissibility preservation**: the swap transport of a binding profile is admissible on the
swapped widths. -/
theorem swapProfile_mem_Adm (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) {T : Fin L → ℕ}
    (hT : T ∈ bindingSet M) :
    swapProfile M k T ∈ Adm (swapWidths k M) := by
  have hlt : k.val - 1 < L := by omega
  obtain ⟨hTadm, hTval⟩ := hT
  obtain ⟨hQX, hXP, hXA, hQA, hQB⟩ := swap_param_range M k hk hTadm
  have hmin := bindingSet_local_min M k hk ⟨hTadm, hTval⟩
  have hYleP := swapR_le_P (A := M k.castSucc) (B := M k.succ) hQX hXP
  have hYleB := swapR_le_B_of_min hQX hXP hXA hQA hQB hmin
  have hTadm2 := hTadm
  rw [Adm, Finset.mem_filter] at hTadm2
  obtain ⟨-, hbT, hdecT, hlastT⟩ := hTadm2
  rw [swapProfile_eq_update M k hk T hlt]
  refine update_mem_Adm (swapWidths k M) k hk _ hlt hdecT hlastT ?_ (swapR_ge_Q hQX hXP) ?_
  · intro j
    by_cases hjkp : j = ⟨k.val - 1, hlt⟩
    · subst hjkp
      rw [Function.update_self]
      by_cases hk1 : k.val = 1
      · unfold admBound
        rw [if_pos (show (⟨k.val - 1, hlt⟩ : Fin L).val = 0 by show k.val - 1 = 0; omega)]
        refine le_min ?_ ?_
        · rw [swapWidths_apply_ne M k (zero_ne_castSucc hk) (zero_ne_succ k)]
          exact le_of_le_of_eq hYleP (if_pos hk1)
        · rw [← castSucc_eq_one k hk1, swapWidths_castSucc]; exact hYleB
      · unfold admBound
        rw [if_neg (show ¬ (⟨k.val - 1, hlt⟩ : Fin L).val = 0 by show ¬ k.val - 1 = 0; omega),
          kpred_succ_eq k hk hlt, swapWidths_castSucc]
        exact hYleB
    · rw [Function.update_of_ne hjkp]
      by_cases hjk : j = k
      · rw [hjk]
        unfold admBound
        rw [if_neg (show ¬ k.val = 0 by omega), swapWidths_succ]
        exact hQA
      · have hjeq : admBound (swapWidths k M) j = admBound M j := by
          unfold admBound
          by_cases hj0 : j.val = 0
          · rw [if_pos hj0, if_pos hj0]
            have hk2 : 2 ≤ k.val := by
              by_contra h; push_neg at h; exact hjkp (Fin.ext (show j.val = k.val - 1 by omega))
            rw [swapWidths_apply_ne M k (zero_ne_castSucc hk) (zero_ne_succ k),
              swapWidths_apply_ne M k (one_ne_castSucc hk2) (one_ne_succ hk2)]
          · rw [if_neg hj0, if_neg hj0,
              swapWidths_apply_ne M k (succ_ne_castSucc hlt hk hjkp) (succ_ne_succ_of_ne hjk)]
        rw [hjeq]; exact hbT j
  · intro hk1; exact le_of_le_of_eq hYleP (if_neg hk1)

/-- **Involution**: two swaps (via the widths-involution) restore the profile. -/
theorem swapProfile_swapProfile (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) {T : Fin L → ℕ}
    (hT : T ∈ Adm M) :
    swapProfile (swapWidths k M) k (swapProfile M k T) = T := by
  have hlt : k.val - 1 < L := by omega
  obtain ⟨hQX, hXP, hXA, hQA, hQB⟩ := swap_param_range M k hk hT
  have hkne : k ≠ (⟨k.val - 1, hlt⟩ : Fin L) := by
    rw [ne_eq, Fin.ext_iff]; show ¬ k.val = k.val - 1; omega
  rw [swapProfile_eq_update M k hk T hlt, swapProfile_eq_update (swapWidths k M) k hk _ hlt,
    Function.update_self, swapWidths_castSucc, swapWidths_succ, Function.update_of_ne hkne]
  -- reduce the outer swapR's first argument `P''` to `P` (the `k−2` else-branch is dead at `k = 1`)
  rw [show (if k.val = 1 then (swapWidths k M) 0
        else (Function.update T ⟨k.val - 1, hlt⟩
          (swapR (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩)
            (T ⟨k.val - 1, hlt⟩) (T k) (M k.castSucc) (M k.succ))) ⟨k.val - 2, by omega⟩)
      = (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) from by
      by_cases hk1 : k.val = 1
      · rw [if_pos hk1, if_pos hk1, swapWidths_apply_ne M k (zero_ne_castSucc hk) (zero_ne_succ k)]
      · rw [if_neg hk1, if_neg hk1, Function.update_of_ne
          (show (⟨k.val - 2, by omega⟩ : Fin L) ≠ ⟨k.val - 1, hlt⟩ by
            rw [ne_eq, Fin.mk.injEq]; show ¬ k.val - 2 = k.val - 1; omega)]]
  rw [swapR_swapR (if k.val = 1 then M 0 else T ⟨k.val - 2, by omega⟩) (T ⟨k.val - 1, hlt⟩)
    (T k) (M k.castSucc) (M k.succ) hQX hXP]
  funext j
  rcases eq_or_ne j (⟨k.val - 1, hlt⟩ : Fin L) with hj | hj
  · subst hj; rw [Function.update_self]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- The swap preserves the admissible minimum value. -/
theorem minAdm_swapWidths_eq (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) :
    (Adm (swapWidths k M)).inf' (Adm_nonempty _) (Mval (swapWidths k M))
      = (Adm M).inf' (Adm_nonempty _) (Mval M) := by
  apply le_antisymm
  · obtain ⟨T, hT, hTval⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
    calc (Adm (swapWidths k M)).inf' (Adm_nonempty _) (Mval (swapWidths k M))
        ≤ Mval (swapWidths k M) (swapProfile M k T) :=
          Finset.inf'_le _ (swapProfile_mem_Adm M k hk ⟨hT, hTval.symm⟩)
      _ = Mval M T := swapProfile_Mval_eq M k hk hT
      _ = (Adm M).inf' (Adm_nonempty _) (Mval M) := hTval.symm
  · obtain ⟨S, hS, hSval⟩ :=
      Finset.exists_mem_eq_inf' (Adm_nonempty (swapWidths k M)) (Mval (swapWidths k M))
    have hSmem : swapProfile (swapWidths k M) k S ∈ Adm M := by
      have h := swapProfile_mem_Adm (swapWidths k M) k hk ⟨hS, hSval.symm⟩
      rwa [swapWidths_swapWidths] at h
    have hSval2 : Mval M (swapProfile (swapWidths k M) k S) = Mval (swapWidths k M) S := by
      have h := swapProfile_Mval_eq (swapWidths k M) k hk hS
      rwa [swapWidths_swapWidths] at h
    calc (Adm M).inf' (Adm_nonempty _) (Mval M)
        ≤ Mval M (swapProfile (swapWidths k M) k S) := Finset.inf'_le _ hSmem
      _ = Mval (swapWidths k M) S := hSval2
      _ = (Adm (swapWidths k M)).inf' (Adm_nonempty _) (Mval (swapWidths k M)) := hSval.symm

/-- The swap transport maps binding profiles to binding profiles. -/
theorem swapProfile_mem_bindingSet (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val)
    {T : Fin L → ℕ} (hT : T ∈ bindingSet M) :
    swapProfile M k T ∈ bindingSet (swapWidths k M) := by
  obtain ⟨hTadm, hTval⟩ := hT
  refine ⟨swapProfile_mem_Adm M k hk ⟨hTadm, hTval⟩, ?_⟩
  rw [swapProfile_Mval_eq M k hk hTadm, hTval]
  exact (minAdm_swapWidths_eq M k hk).symm

/-- **Coupled monotonicity of the transport** on binding profiles. -/
theorem swapProfile_mono (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : 0 < k.val) {T T' : Fin L → ℕ}
    (hT : T ∈ bindingSet M) (hT' : T' ∈ bindingSet M) (hle : T ≤ T') :
    swapProfile M k T ≤ swapProfile M k T' := by
  have hlt : k.val - 1 < L := by omega
  obtain ⟨hTadm, hTval⟩ := hT
  obtain ⟨hT'adm, hT'val⟩ := hT'
  obtain ⟨hQX, hXP, hXA, hQA, hQB⟩ := swap_param_range M k hk hTadm
  obtain ⟨hQX', hXP', hXA', hQA', hQB'⟩ := swap_param_range M k hk hT'adm
  have hminT := bindingSet_local_min M k hk ⟨hTadm, hTval⟩
  have hminT' := bindingSet_local_min M k hk ⟨hT'adm, hT'val⟩
  have hle' := Pi.le_def.mp hle
  rw [Pi.le_def]
  intro j
  rw [swapProfile_eq_update M k hk T hlt, swapProfile_eq_update M k hk T' hlt]
  rcases eq_or_ne j (⟨k.val - 1, hlt⟩ : Fin L) with hj | hj
  · subst hj
    rw [Function.update_self, Function.update_self]
    refine swapR_mono_of_min hQX hXP hXA hQA hQB hQX' hXP' hXA' hQA' hQB' ?_ (hle' _) (hle' _)
      hminT hminT'
    by_cases hk1 : k.val = 1
    · simp [hk1]
    · rw [if_neg hk1, if_neg hk1]; exact hle' _
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]; exact hle' j

/-! ## The `k = 0` degenerate case (transport is the identity) -/

/-- Swapping the first two widths leaves `Adm` unchanged (`admBound` is symmetric at `j = 0`). -/
theorem Adm_swapWidths_zero (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : k.val = 0) :
    Adm (swapWidths k M) = Adm M := by
  have hcs : k.castSucc = (0 : Fin (L + 1)) := by
    rw [Fin.ext_iff, Fin.coe_castSucc, Fin.val_zero]; exact hk
  have hsc : k.succ = (1 : Fin (L + 1)) := by
    rw [Fin.ext_iff, Fin.val_succ, hk, Fin.val_one', Nat.mod_eq_of_lt (by have := k.isLt; omega)]
  have hab : ∀ j : Fin L, admBound (swapWidths k M) j = admBound M j := by
    intro j
    unfold admBound
    by_cases hj0 : j.val = 0
    · rw [if_pos hj0, if_pos hj0,
        show (swapWidths k M) 0 = M 1 by
          simp only [swapWidths, Function.comp_apply, hcs, hsc, Equiv.swap_apply_left],
        show (swapWidths k M) 1 = M 0 by
          simp only [swapWidths, Function.comp_apply, hcs, hsc, Equiv.swap_apply_right],
        Nat.min_comm]
    · rw [if_neg hj0, if_neg hj0]
      apply swapWidths_apply_ne
      · rw [hcs, ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_zero]; omega
      · rw [hsc, ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_one',
          Nat.mod_eq_of_lt (by have := k.isLt; omega)]; omega
  ext T
  simp only [Adm, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, admPred, hab]

/-- Swapping the first two widths leaves `Mval` unchanged (the `j = 0` term is symmetric). -/
theorem Mval_swapWidths_zero (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : k.val = 0) (T : Fin L → ℕ) :
    Mval (swapWidths k M) T = Mval M T := by
  have hcs : k.castSucc = (0 : Fin (L + 1)) := by
    rw [Fin.ext_iff, Fin.coe_castSucc, Fin.val_zero]; exact hk
  have hsc : k.succ = (1 : Fin (L + 1)) := by
    rw [Fin.ext_iff, Fin.val_succ, hk, Fin.val_one', Nat.mod_eq_of_lt (by have := k.isLt; omega)]
  rw [Mval_eq_sum_mvTerm, Mval_eq_sum_mvTerm]
  apply Finset.sum_congr rfl
  intro j _
  unfold mvTerm tPrev
  by_cases hj0 : j.val = 0
  · have hjs : j.succ = (1 : Fin (L + 1)) := by
      rw [Fin.ext_iff, Fin.val_succ, hj0, Fin.val_one',
        Nat.mod_eq_of_lt (by have := k.isLt; omega)]
    rw [if_pos hj0, if_pos hj0, hjs,
      show (swapWidths k M) 0 = M 1 by
        simp only [swapWidths, Function.comp_apply, hcs, hsc, Equiv.swap_apply_left],
      show (swapWidths k M) 1 = M 0 by
        simp only [swapWidths, Function.comp_apply, hcs, hsc, Equiv.swap_apply_right]]
    ring
  · rw [if_neg hj0, if_neg hj0,
      swapWidths_apply_ne M k
        (show j.succ ≠ k.castSucc by
          rw [hcs, ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_zero]; omega)
        (show j.succ ≠ k.succ by
          rw [hsc, ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_one',
            Nat.mod_eq_of_lt (by have := k.isLt; omega)]; omega)]

/-- The swap preserves the admissible minimum value (degenerate `k = 0`). -/
theorem minAdm_swapWidths_zero (M : Fin (L + 1) → ℕ) (k : Fin L) (hk : k.val = 0) :
    (Adm (swapWidths k M)).inf' (Adm_nonempty _) (Mval (swapWidths k M))
      = (Adm M).inf' (Adm_nonempty _) (Mval M) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro T hT
    have hT' : T ∈ Adm (swapWidths k M) := (Adm_swapWidths_zero M k hk).symm ▸ hT
    calc (Adm (swapWidths k M)).inf' (Adm_nonempty _) (Mval (swapWidths k M))
        ≤ Mval (swapWidths k M) T := Finset.inf'_le _ hT'
      _ = Mval M T := Mval_swapWidths_zero M k hk T
  · apply Finset.le_inf'
    intro T hT
    have hT' : T ∈ Adm M := Adm_swapWidths_zero M k hk ▸ hT
    calc (Adm M).inf' (Adm_nonempty _) (Mval M)
        ≤ Mval M T := Finset.inf'_le _ hT'
      _ = Mval (swapWidths k M) T := (Mval_swapWidths_zero M k hk T).symm

/-! ## Assembly -/

/-- **(a)+(b) — the one-swap order-iso** (delivers `OrderRealize.swapBinding_orderIso`): one
adjacent width-swap is an order-isomorphism of the binding poset via the `swapR` transport. -/
theorem swapBinding_orderIso_impl (M : Fin (L + 1) → ℕ) (k : Fin L) (hpos : ∀ s, 0 < M s) :
    Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (swapWidths k M))) := by
  rcases Nat.eq_zero_or_pos k.val with hk0 | hk
  · -- `k = 0`: the swap fixes `bindingSet` (both `Adm` and `Mval` are symmetric at `j = 0`)
    have hset : bindingSet (swapWidths k M) = bindingSet M := by
      ext T
      simp only [bindingSet, Set.mem_setOf_eq, Adm_swapWidths_zero M k hk0,
        Mval_swapWidths_zero M k hk0, minAdm_swapWidths_zero M k hk0]
    exact ⟨OrderIso.setCongr _ _ hset.symm⟩
  · -- `k ≥ 1`: the `swapProfile` transport with its monotone inverse
    exact ⟨{
      toEquiv :=
        { toFun := fun T => ⟨swapProfile M k T.1, swapProfile_mem_bindingSet M k hk T.2⟩
          invFun := fun S => ⟨swapProfile (swapWidths k M) k S.1, by
            have h := swapProfile_mem_bindingSet (swapWidths k M) k hk S.2
            rwa [swapWidths_swapWidths] at h⟩
          left_inv := fun T => Subtype.ext (swapProfile_swapProfile M k hk T.2.1)
          right_inv := fun S => Subtype.ext (by
            have h := swapProfile_swapProfile (swapWidths k M) k hk S.2.1
            rwa [swapWidths_swapWidths] at h) }
      map_rel_iff' := by
        intro a b
        constructor
        · intro h
          have hm := swapProfile_mono (swapWidths k M) k hk
            (swapProfile_mem_bindingSet M k hk a.2) (swapProfile_mem_bindingSet M k hk b.2) h
          rwa [swapProfile_swapProfile M k hk a.2.1, swapProfile_swapProfile M k hk b.2.1] at hm
        · intro h
          exact swapProfile_mono M k hk a.2 b.2 h }⟩

end DLNFibre.DLN.Aoyagi
