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

end DLNFibre.Core.Matrix
