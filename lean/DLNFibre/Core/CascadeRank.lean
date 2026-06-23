import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.Fin

/-!
# `DLNFibre.Core.CascadeRank` — the rank of rectangular partial-identity ("cascade") blocks

The count-the-1s rank lever for the diagonal-cascade realizability (pp2 g228, the §4 achiever witness):
a cascade block `C_s = diag(1^t, 0)` is a rectangular partial-identity, and the rank of any product of
such blocks is the number of surviving 1s (a window-min of the cascade ranks) — NOT a hard rank theorem
(no `Matrix.rank_mul_le`, no surjectivity), just the column-span count.

Mathlib's `Matrix.rank_diagonal` is SQUARE-only; the rectangular case here goes via the column-span
characterization `rank_eq_finrank_span_cols` + the standard-basis independence
`Pi.linearIndependent_single_of_ne_zero` (the same mechanism `rank_diagonal` uses internally).

This is rung 1 of the cascade-realizability ladder (Core, network-free).
-/

open Matrix
namespace DLNFibre.Core

variable {k : Type*} [Field k]

/-- The rectangular partial-identity block `diag(1^t, 0) : Matrix (Fin r) (Fin c) k`: entry `(i,j)` is
`1` when `i = j` (as naturals) and `i < t`, else `0`. The `s`-th cascade block has `t = t_{s+1}`. Over an
abstract field `k` (the Core `Tuple` convention). -/
def partialId (k : Type*) [Field k] (r c t : ℕ) : Matrix (Fin r) (Fin c) k :=
  Matrix.of (fun i j => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < t then (1 : k) else 0)

/-- The number of surviving 1s in `partialId r c t`: `min t (min r c)`. -/
def survivors (r c t : ℕ) : ℕ := min t (min r c)

/-- **Rung 1 — the rectangular partial-identity rank (the count-the-1s atom).** The rank of the cascade
block `diag(1^t, 0) : Matrix (Fin r) (Fin c) k` is the number of surviving 1s, `min t (min r c)`. Mathlib's
`rank_diagonal` is square-only; this is the rectangular case via the column-span characterization. -/
theorem rank_partialId (r c t : ℕ) : (partialId k r c t).rank = survivors r c t := by
  classical
  -- The nonzero columns of `partialId` are the distinct standard basis vectors `e_j` for
  -- `j < survivors = min t (min r c)`; the span of the columns = span of those, finrank = survivors.
  rw [Matrix.rank_eq_finrank_span_cols]
  -- the basis-vector family indexed by `Fin (survivors r c t)`.
  set N := survivors r c t with hN
  have hNr : N ≤ r := le_trans (min_le_right _ _) (min_le_left _ _)
  have hNc : N ≤ c := le_trans (min_le_right _ _) (min_le_right _ _)
  have hNt : N ≤ t := min_le_left _ _
  -- b i = e_{i} : Fin r → k (standard basis), i : Fin N embedded into Fin r.
  let emb : Fin N → Fin r := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hNr⟩
  let b : Fin N → (Fin r → k) := fun i => Pi.single (emb i) 1
  have hembinj : Function.Injective emb := by
    intro i j hij
    exact Fin.ext (by simpa [emb] using congrArg Fin.val hij)
  have hbli : LinearIndependent k b :=
    (Pi.linearIndependent_single_of_ne_zero (R := k) (v := fun _ : Fin r => (1 : k))
      (fun _ => one_ne_zero)).comp emb hembinj
  have hspan : Submodule.span k (Set.range (partialId k r c t).col)
      = Submodule.span k (Set.range b) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      -- column j: if (j:ℕ) < t ∧ (j:ℕ) < r then e_j (∈ range b iff j < N) else 0.
      by_cases hj : (j : ℕ) < t ∧ (j : ℕ) < r
      · have hjN : (j : ℕ) < N := by
          rw [hN, survivors]; exact lt_min hj.1 (lt_min hj.2 j.isLt)
        have hcol : (partialId k r c t).col j = b ⟨(j : ℕ), hjN⟩ := by
          funext i
          simp only [Matrix.col, Matrix.transpose_apply, partialId, Matrix.of_apply, b, emb,
            Pi.single_apply]
          have hiff : ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < t) ↔ (⟨(j:ℕ), hj.2⟩ : Fin r) = i := by
            constructor
            · rintro ⟨hij, _⟩; exact Fin.ext hij.symm
            · intro h; exact ⟨(Fin.ext_iff.1 h).symm, by rw [← (Fin.ext_iff.1 h)]; exact hj.1⟩
          by_cases hc : (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < t
          · rw [if_pos hc, if_pos (hiff.1 hc).symm]
          · rw [if_neg hc, if_neg (fun h => hc (hiff.2 h.symm))]
        rw [hcol]
        exact Submodule.subset_span ⟨_, rfl⟩
      · have hcol : (partialId k r c t).col j = 0 := by
          funext i
          simp only [Matrix.col, Matrix.transpose_apply, partialId, Matrix.of_apply, Pi.zero_apply]
          have hne : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < t) := by
            rintro ⟨hij, hit⟩
            exact hj ⟨hij ▸ hit, hij ▸ i.isLt⟩
          simp [hne]
        rw [hcol]; exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hcol : (partialId k r c t).col ⟨i.val, lt_of_lt_of_le i.isLt hNc⟩ = b i := by
        funext i'
        simp only [Matrix.col, Matrix.transpose_apply, partialId, Matrix.of_apply, b, emb,
          Pi.single_apply]
        have hit : (i : ℕ) < t := lt_of_lt_of_le i.isLt hNt
        have hiff : ((i' : ℕ) = (i : ℕ) ∧ (i' : ℕ) < t)
            ↔ (⟨(i:ℕ), lt_of_lt_of_le i.isLt hNr⟩ : Fin r) = i' := by
          constructor
          · rintro ⟨hii, _⟩; exact Fin.ext hii.symm
          · intro h; exact ⟨(Fin.ext_iff.1 h).symm, by rw [← (Fin.ext_iff.1 h)]; exact hit⟩
        by_cases hc : (i' : ℕ) = (i : ℕ) ∧ (i' : ℕ) < t
        · rw [if_pos hc, if_pos (hiff.1 hc).symm]
        · rw [if_neg hc, if_neg (fun h => hc (hiff.2 h.symm))]
      rw [← hcol]; exact Submodule.subset_span ⟨_, rfl⟩
  rw [hspan, finrank_span_eq_card hbli, Fintype.card_fin]

/-- **Rung 3 atom — the partial-identity product law (the window-min step).** With the surviving rank
bounded by the middle dimension (`a ≤ m`, the cascade's `t_{s+1} ≤ M_{s+1}` admissibility), a product of
two cascade blocks is again a partial-identity, surviving-1 count the `min`:
`partialId r m a * partialId m c b = partialId r c (min a b)`. The entry
`(P_a · P_b) i j = ∑_l P_a i l · P_b l j` is nonzero only when `l = i = j` with `i < a, i < b`, i.e.
`i = j ∧ i < min a b` (and `i < a ≤ m` makes `l = i` a valid middle index). Iterating this gives the
cascade window-min (the count-the-1s lever). -/
theorem partialId_mul (r m c a b : ℕ) (ha : a ≤ m) :
    (partialId k r m a) * (partialId k m c b) = partialId k r c (min a b) := by
  ext i j
  simp only [Matrix.mul_apply, partialId, Matrix.of_apply]
  by_cases hsurv : (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < min a b
  · obtain ⟨hij, hlt⟩ := hsurv
    have hia : (i : ℕ) < a := lt_of_lt_of_le hlt (min_le_left _ _)
    have hib : (i : ℕ) < b := lt_of_lt_of_le hlt (min_le_right _ _)
    have him : (i : ℕ) < m := lt_of_lt_of_le hia ha
    rw [if_pos ⟨hij, hlt⟩, Finset.sum_eq_single (⟨(i : ℕ), him⟩ : Fin m)]
    · rw [if_pos ⟨rfl, hia⟩, if_pos ⟨hij ▸ rfl, hib⟩, mul_one]
    · intro l _ hl
      have hli : (l : ℕ) ≠ (i : ℕ) := fun h => hl (Fin.ext h)
      rw [if_neg (fun hc => hli hc.1.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hsurv]
    apply Finset.sum_eq_zero
    intro l _
    by_cases h1 : (i : ℕ) = (l : ℕ) ∧ (i : ℕ) < a
    · rw [if_pos h1, one_mul]
      exact if_neg (fun h2 => hsurv ⟨h1.1.trans h2.1, lt_min h1.2 (h1.1 ▸ h2.2)⟩)
    · rw [if_neg h1, zero_mul]

end DLNFibre.Core
