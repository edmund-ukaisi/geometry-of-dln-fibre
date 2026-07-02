import DLNFibre.Core.Matrix.DiagDominance

/-!
# `Core.Matrix.CarrierBlock` — the carrier-block distinguished-path determinant bound

A network-free engine brick. For a product of "carrier layers" (real matrices whose top-left `r×r`
carrier block has a large diagonal `∈ [δ/2, δ]`, small carrier off-diagonal, and small off-carrier
entries, all other entries small in absolute value `≤ η`), the top-left `r×r` block of the product
is **strictly row diagonally dominant**, hence invertible (`det ≠ 0`).

The design (pen-and-paper certificate `/tmp/r1design/codex-answer.md`): the top-left block of a
chain product `A⁰·…·A^{n−1}` restricted to the first `r` indices has, on its diagonal, one
distinguished all-carrier path `≥ (δ/2)ⁿ`, and every other path carries an `η`-small factor.
The clean formalisation route is a **two-sided entrywise invariant** carried inductively over the
layer count: track a diagonal lower bound `dlb` and an off-diagonal upper bound `oub` for the
carrier block, then `StrictRowDominant` follows once `dlb > (r−1)·oub`.

* `CarrierBound P dlb oub` — the two-sided invariant on an `r×r` block `P`: `dlb ≤ |P i i|` and
  `|P i j| ≤ oub` for `i ≠ j`.
* `CarrierBound.strictRowDominant` — a `CarrierBound` with `(r−1)·oub < dlb` gives
  `StrictRowDominant` with margin `dlb − (r−1)·oub`; `CarrierBound.det_ne_zero` the det corollary.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.Core.Matrix

variable {r : ℕ}

/-- **The two-sided carrier invariant.** The `r×r` matrix `P` has every diagonal entry `≥ dlb`
in absolute value and every off-diagonal entry `≤ oub` in absolute value. -/
def CarrierBound (P : Matrix (Fin r) (Fin r) ℝ) (dlb oub : ℝ) : Prop :=
  (∀ i, dlb ≤ |P i i|) ∧ (∀ i j, i ≠ j → |P i j| ≤ oub)

/-- A `CarrierBound` with strictly-dominated off-diagonal (`(r−1)·oub < dlb`) is strictly row
diagonally dominant with margin `dlb − (r−1)·oub`. -/
theorem CarrierBound.strictRowDominant {P : Matrix (Fin r) (Fin r) ℝ} {dlb oub : ℝ}
    (h : CarrierBound P dlb oub) (hdom : (r - 1 : ℝ) * oub < dlb) :
    StrictRowDominant P (dlb - (r - 1 : ℝ) * oub) := by
  obtain ⟨hdiag, hoff⟩ := h
  refine ⟨by linarith, fun k => ?_⟩
  -- `r ≥ 1` since `Fin r` is inhabited by `k`
  have hrpos : 0 < r := k.pos
  -- off-diagonal row-sum `≤ (r−1)·oub`
  have hcard : (Finset.univ.erase k).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have hsum : (∑ j ∈ Finset.univ.erase k, |P k j|) ≤ (r - 1 : ℝ) * oub := by
    calc (∑ j ∈ Finset.univ.erase k, |P k j|)
        ≤ ∑ _j ∈ Finset.univ.erase k, oub :=
          Finset.sum_le_sum (fun j hj => hoff k j (fun h => (Finset.mem_erase.mp hj).1 h.symm))
      _ = ((r - 1 : ℕ) : ℝ) * oub := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ = (r - 1 : ℝ) * oub := by rw [Nat.cast_sub hrpos, Nat.cast_one]
  linarith [hdiag k]

/-- **`det ≠ 0` for a strictly-dominated carrier block** (Levy–Desplanques). -/
theorem CarrierBound.det_ne_zero {P : Matrix (Fin r) (Fin r) ℝ} {dlb oub : ℝ}
    (h : CarrierBound P dlb oub) (hdom : (r - 1 : ℝ) * oub < dlb) :
    P.det ≠ 0 :=
  (h.strictRowDominant hdom).det_ne_zero

/-! ## The wide carrier invariant + the one-step layer composition

The inductive object is a partial product `P : Fin r → Fin w → ℝ` (an `r × w` matrix — the first `r`
rows of the chain product so far, `w` the current interface width). We track three quantities:

* `dlb ≤ |P i i|` for the carrier diagonal (`i < r`);
* `|P i j| ≤ nb` for every NON-distinguished entry (anything but a carrier diagonal `i = j < r`);
* `|P i j| ≤ pub` for EVERY entry (the global upper bound).

`nb` is the bound that matters for the row-sum, `pub` the one that propagates the cross-terms. A
`CarrierLayer A r δ η` matrix (carrier diagonal `∈ [δ/2, δ]`, every other entry `≤ η`) advances the
product `P → P · A` with the linear recursion below (`wideCarrier_mul`). -/

/-- **The wide carrier invariant** on an `r × w` partial product `P`. -/
def WideCarrierBound {w : ℕ} (P : Matrix (Fin r) (Fin w) ℝ) (dlb nb pub : ℝ) : Prop :=
  (∀ i : Fin r, ∀ hi : (i : ℕ) < w, dlb ≤ |P i ⟨i, hi⟩|)
    ∧ (∀ i : Fin r, ∀ j : Fin w, (j : ℕ) ≠ (i : ℕ) → |P i j| ≤ nb)
    ∧ (∀ i j, |P i j| ≤ pub)

/-- **A carrier layer** `A : Fin w → Fin w' → ℝ`: the carrier diagonal (`i = j < r`) `∈ [δ/2, δ]`,
every other entry `≤ η` in absolute value. The building block of the chain product. -/
def CarrierLayer {w w' : ℕ} (A : Matrix (Fin w) (Fin w') ℝ) (r : ℕ) (δ η : ℝ) : Prop :=
  (∀ i : Fin w, ∀ j : Fin w', (i : ℕ) = (j : ℕ) → (i : ℕ) < r → A i j ∈ Set.Icc (δ / 2) δ)
    ∧ (∀ i : Fin w, ∀ j : Fin w', ¬((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r) → |A i j| ≤ η)

/-- A carrier layer's every entry is bounded by `δ` (`η ≤ δ`, carrier diag `≤ δ`). -/
theorem CarrierLayer.entry_le {w w' : ℕ} {A : Matrix (Fin w) (Fin w') ℝ} {δ η : ℝ}
    (hA : CarrierLayer A r δ η) (hηδ : η ≤ δ) (i : Fin w) (j : Fin w') : |A i j| ≤ δ := by
  by_cases h : (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r
  · have hmem := hA.1 i j h.1 h.2
    rw [Set.mem_Icc] at hmem
    -- `δ/2 ≤ A i j ≤ δ` forces `δ ≥ 0`, hence `0 ≤ δ/2 ≤ A i j`
    rw [abs_of_nonneg (by linarith [hmem.1, hmem.2] : (0:ℝ) ≤ A i j)]
    exact hmem.2
  · exact (hA.2 i j h).trans hηδ

/-- **The distinguished carrier-diagonal factor.** For a carrier layer, `A ⟨i,_⟩ ⟨i,_⟩ ≥ δ/2` at a
carrier index `i < r`. -/
theorem CarrierLayer.diag_ge {w w' : ℕ} {A : Matrix (Fin w) (Fin w') ℝ} {δ η : ℝ}
    (hA : CarrierLayer A r δ η) {i : ℕ} (hiw : i < w) (hiw' : i < w') (hir : i < r) :
    δ / 2 ≤ A ⟨i, hiw⟩ ⟨i, hiw'⟩ :=
  (Set.mem_Icc.mp (hA.1 ⟨i, hiw⟩ ⟨i, hiw'⟩ rfl hir)).1

/-- A carrier-layer entry off the carrier diagonal is `≤ η`: any `A k j` with `(k,j)` not a
carrier-diagonal position. -/
theorem CarrierLayer.offdiag_le {w w' : ℕ} {A : Matrix (Fin w) (Fin w') ℝ} {δ η : ℝ}
    (hA : CarrierLayer A r δ η) (k : Fin w) (j : Fin w') (h : ¬((k : ℕ) = (j : ℕ) ∧ (k : ℕ) < r)) :
    |A k j| ≤ η := hA.2 k j h

/-! ## The one-step layer composition (the crux, distinguished-path made inductive)

`wideCarrier_mul`: multiplying a partial product `P` (satisfying `WideCarrierBound P dlb nb pub`) by
a `CarrierLayer A r δ η` advances the invariant to `P · A` with the linear recursion

* `dlb' = dlb·(δ/2) − (w−1)·pub·η`   (distinguished term minus the `w−1` η-small cross terms);
* `nb'  = nb·δ + w·pub·η`            (every non-distinguished target carries an η-small factor);
* `pub' = w·pub·δ`                   (crude global bound, `w` terms each `≤ pub·δ`).

The bounds require `0 ≤ pub`, `0 ≤ η ≤ δ`, and `0 ≤ nb`. -/

/-- **The one-step layer composition** (the crux). Advances `WideCarrierBound` across one
`CarrierLayer`. See the module note for the recursion. -/
theorem wideCarrier_mul {w w' : ℕ} {P : Matrix (Fin r) (Fin w) ℝ} {A : Matrix (Fin w) (Fin w') ℝ}
    {dlb nb pub δ η : ℝ} (hP : WideCarrierBound P dlb nb pub) (hA : CarrierLayer A r δ η)
    (hpub : 0 ≤ pub) (hnb : 0 ≤ nb) (hη : 0 ≤ η) (hηδ : η ≤ δ) (hrw : r ≤ w) :
    WideCarrierBound (P * A) (dlb * (δ / 2) - (w - 1 : ℕ) * pub * η)
      (nb * δ + w * pub * η) (w * pub * δ) := by
  obtain ⟨hPdiag, hPnb, hPpub⟩ := hP
  have hδ0 : 0 ≤ δ := le_trans hη hηδ
  -- global bound helper: every `|A k j| ≤ δ`
  have hAδ : ∀ (k : Fin w) (j : Fin w'), |A k j| ≤ δ := hA.entry_le hηδ
  -- the product entry
  have hmul : ∀ (i : Fin r) (j : Fin w'), (P * A) i j = ∑ k : Fin w, P i k * A k j :=
    fun i j => Matrix.mul_apply
  refine ⟨?_, ?_, ?_⟩
  · -- new carrier diagonal lower bound
    intro i hiw'
    have hiw : (i : ℕ) < w := lt_of_lt_of_le i.isLt hrw
    have hir : (i : ℕ) < r := i.isLt
    rw [hmul]
    -- isolate `k = ⟨i, hiw⟩`
    set kd : Fin w := ⟨i, hiw⟩ with hkd
    have hsplit : (∑ k : Fin w, P i k * A k ⟨i, hiw'⟩)
        = P i kd * A kd ⟨i, hiw'⟩ + ∑ k ∈ Finset.univ.erase kd, P i k * A k ⟨i, hiw'⟩ := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ kd)]; ring
    rw [hsplit]
    -- distinguished term `≥ dlb·(δ/2)`
    have hdist : dlb * (δ / 2) ≤ |P i kd * A kd ⟨i, hiw'⟩| := by
      rw [abs_mul]
      have h1 : dlb ≤ |P i kd| := by
        have := hPdiag i hiw
        simpa [hkd] using this
      have h2 : δ / 2 ≤ |A kd ⟨i, hiw'⟩| := by
        have := hA.diag_ge hiw hiw' hir
        rw [abs_of_nonneg (le_trans (by linarith) this)]
        exact this
      calc dlb * (δ / 2) ≤ |P i kd| * (δ / 2) :=
              mul_le_mul_of_nonneg_right h1 (by linarith)
        _ ≤ |P i kd| * |A kd ⟨i, hiw'⟩| := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    -- cross terms `≤ (w−1)·pub·η`
    have hcross : |∑ k ∈ Finset.univ.erase kd, P i k * A k ⟨i, hiw'⟩| ≤ (w - 1 : ℕ) * pub * η := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hbound : ∀ k ∈ Finset.univ.erase kd, |P i k * A k ⟨i, hiw'⟩| ≤ pub * η := by
        intro k hk
        rw [abs_mul]
        have hkne : k ≠ kd := (Finset.mem_erase.mp hk).1
        have hAke : |A k ⟨i, hiw'⟩| ≤ η := by
          refine hA.offdiag_le k ⟨i, hiw'⟩ (fun ⟨hkv, _⟩ => hkne ?_)
          exact Fin.ext (by simp only [hkd]; omega)
        exact mul_le_mul (hPpub i k) hAke (abs_nonneg _) hpub
      calc (∑ k ∈ Finset.univ.erase kd, |P i k * A k ⟨i, hiw'⟩|)
          ≤ ∑ _k ∈ Finset.univ.erase kd, pub * η := Finset.sum_le_sum hbound
        _ = (Finset.univ.erase kd).card * (pub * η) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = (w - 1 : ℕ) * (pub * η) := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ kd), Finset.card_univ, Fintype.card_fin]
        _ = (w - 1 : ℕ) * pub * η := by ring
    -- combine: `|dist + cross| ≥ |dist| − |cross| ≥ dlb(δ/2) − (w−1)pubη`
    set S : ℝ := ∑ k ∈ Finset.univ.erase kd, P i k * A k ⟨i, hiw'⟩ with hS
    set D : ℝ := P i kd * A kd ⟨i, hiw'⟩ with hD
    have htri : |D| - |S| ≤ |D + S| := by
      -- `|D| = |(D+S) − S| ≤ |D+S| + |S|`
      have h := abs_sub (D + S) S
      rw [add_sub_cancel_right] at h
      linarith [h]
    linarith [hdist, hcross, htri]
  · -- new non-distinguished upper bound `nb·δ + w·pub·η`
    intro i j hji
    rw [hmul]
    -- Does column `j` carry a carrier-diagonal `A`-entry? iff `(j:ℕ) < r` (at row `k=j`).
    by_cases hjr : (j : ℕ) < r
    · -- distinguished `A`-term at `k = ⟨j, hjw⟩`; here `P i ⟨j,·⟩` is non-distinguished (`j ≠ i`)
      have hjw : (j : ℕ) < w := lt_of_lt_of_le hjr hrw
      set kj : Fin w := ⟨j, hjw⟩ with hkj
      have hsplit : (∑ k : Fin w, P i k * A k j)
          = P i kj * A kj j + ∑ k ∈ Finset.univ.erase kj, P i k * A k j := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ kj)]; ring
      rw [hsplit]
      -- distinguished term `≤ nb·δ`
      have hd : |P i kj * A kj j| ≤ nb * δ := by
        rw [abs_mul]
        have hP : |P i kj| ≤ nb := hPnb i kj (by simp only [hkj]; omega)
        exact mul_le_mul hP (hAδ kj j) (abs_nonneg _) hnb
      -- cross terms `≤ (w−1)·pub·η ≤ w·pub·η`
      have hc : |∑ k ∈ Finset.univ.erase kj, P i k * A k j| ≤ w * pub * η := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hbound : ∀ k ∈ Finset.univ.erase kj, |P i k * A k j| ≤ pub * η := by
          intro k hk
          rw [abs_mul]
          have hkne : k ≠ kj := (Finset.mem_erase.mp hk).1
          have hAke : |A k j| ≤ η := by
            refine hA.offdiag_le k j (fun ⟨hkv, _⟩ => hkne ?_)
            exact Fin.ext (by simp only [hkj]; omega)
          exact mul_le_mul (hPpub i k) hAke (abs_nonneg _) hpub
        calc (∑ k ∈ Finset.univ.erase kj, |P i k * A k j|)
            ≤ ∑ _k ∈ Finset.univ.erase kj, pub * η := Finset.sum_le_sum hbound
          _ = (Finset.univ.erase kj).card * (pub * η) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ w * (pub * η) := by
                rw [Finset.card_erase_of_mem (Finset.mem_univ kj), Finset.card_univ, Fintype.card_fin]
                have : ((w - 1 : ℕ) : ℝ) ≤ (w : ℝ) := by
                  rw [← Nat.cast_le (α := ℝ)] at *; exact_mod_cast Nat.sub_le w 1
                exact mul_le_mul_of_nonneg_right this (mul_nonneg hpub hη)
          _ = w * pub * η := by ring
      calc |P i kj * A kj j + ∑ k ∈ Finset.univ.erase kj, P i k * A k j|
          ≤ |P i kj * A kj j| + |∑ k ∈ Finset.univ.erase kj, P i k * A k j| := abs_add_le _ _
        _ ≤ nb * δ + w * pub * η := by linarith [hd, hc]
    · -- no carrier-diagonal `A`-term: every `A k j` is η-small, total `≤ w·pub·η ≤ nb·δ + w·pub·η`
      have hall : |∑ k : Fin w, P i k * A k j| ≤ w * pub * η := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hbound : ∀ k : Fin w, |P i k * A k j| ≤ pub * η := by
          intro k
          rw [abs_mul]
          have hAke : |A k j| ≤ η := hA.offdiag_le k j (fun ⟨hkeq, hjrr⟩ => hjr (by omega))
          exact mul_le_mul (hPpub i k) hAke (abs_nonneg _) hpub
        calc (∑ k : Fin w, |P i k * A k j|) ≤ ∑ _k : Fin w, pub * η := Finset.sum_le_sum
              (fun k _ => hbound k)
          _ = w * (pub * η) := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
              Fintype.card_fin]
          _ = w * pub * η := by ring
      have : (0:ℝ) ≤ nb * δ := mul_nonneg hnb hδ0
      linarith [hall]
  · -- new global upper bound `w·pub·δ`
    intro i j
    rw [hmul]
    calc |∑ k : Fin w, P i k * A k j| ≤ ∑ k : Fin w, |P i k * A k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin w, pub * δ := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [abs_mul]; exact mul_le_mul (hPpub i k) (hAδ k j) (abs_nonneg _) hpub
      _ = w * (pub * δ) := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      _ = w * pub * δ := by ring

end DLNFibre.Core.Matrix
