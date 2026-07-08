import DLNFibre.DLN.RLCT.Foundations.Loss
import DLNFibre.Core.CommonPivotL2

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeCommonPivot` — the general-`L` common (prefix) pivot

Piece (i) of the D1 `≥`-leg chart data: the general-`L` lift of `exists_common_pivot_L2_at`
(`D1L2PhiExpl`). At an optimal `v` (`prod H v = B`, `B.rank = r`), it produces a per-VERTEX family
of injections `ι : (s : Fin (L+1)) → Fin r → Fin (H s)` — one pivot index set per vertex, the shape
`D1GeBlockModel`'s block model consumes — such that EVERY prefix-product minor is invertible:

    for all `s`,  `(prodAux H v s).submatrix (ι 0) (ι s)` has nonzero determinant.

The shared row set `ι 0` (at the output vertex `0`) anchors all prefix minors. At `L = 2` this is
exactly the L = 2 template: the `s = 1` minor is `(v 0).submatrix (ι 0) (ι 1)` (the first-layer /
prefix-1 pivot `X`) and the `s = 2` minor is `(prod H v).submatrix (ι 0) (ι 2)` (the product pivot
`M11`); there is no separate interior-layer condition — matching `exists_common_pivot_L2_at`, which
is purely prefix conditions.

**No Cauchy–Binet** (Mathlib v4.29 lacks a rectangular Cauchy–Binet), by the same rank squeeze as
`Core.exists_common_pivot_two_factor`, iterated with a FIXED row set `ι 0`: pick `ι 0` and a column
set from a full-product invertible minor (`exists_square_minor`); then for each `s`, the split
`prod H v = (prodAux H v s) · Y` forces `(prodAux H v s).submatrix (ι 0) id` to have rank `r`
(rank squeeze via `rank_mul_le_left`), so it has an invertible `r`-column minor, transported back to
the row set `ι 0` by a row permutation (`det_permute`). This delivers the `hPart` (partial-product
pivot) obligations of the general-`L` Schur telescope.

**Not delivered here (reported sub-gap): the per-LAYER pivots `hLayer`** (`(v s).submatrix (ι s)
(ι (s+1))` invertible for every layer), which the symmetric `schur_product_ldu_rec` also demands.
Those genuinely need Cauchy–Binet (`det(A·B) = ∑_K det A[·,K] · det B[K,·]`): the rank squeeze gives
only one side of a two-factor pivot, not both. The general-`L` chart AVOIDS them by iterating the
asymmetric two-factor `schur_product_factor` (each step `(prefix P_s)·(layer v_s)` needs only the
two prefix pivots `P_s`, `P_{s+1}`, never an interior layer's own minor), so the prefix pivots here
suffice. (Cited decorrelation: local Codex, `threads/genm-geleg1/codex/piece-i-statement-*.md`.)
-/

open Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The prefix-product split.** The prefix product through all `L` layers factors at any earlier
position `p ≤ L`: `prodAux H v L = prodAux H v p · Y`. The `L = k`-endpoint specialisation of the
interior split, reproved locally (only `prodAux_succ` + `Matrix.mul_assoc`) to keep this module's
import closure minimal. -/
private theorem prodAux_split_full (H : Fin (L + 1) → ℕ) (v : Params H) (p : ℕ) (hp : p < L + 1) :
    ∀ (k : ℕ) (_hpk : p ≤ k) (hk : k < L + 1),
      ∃ (Y : Matrix (Fin (H ⟨p, hp⟩)) (Fin (H ⟨k, hk⟩)) ℝ),
        prodAux H v k hk = prodAux H v p hp * Y := by
  intro k hpk
  induction k, hpk using Nat.le_induction with
  | base =>
      intro hk
      obtain rfl : hk = hp := Subsingleton.elim _ _
      exact ⟨1, (Matrix.mul_one _).symm⟩
  | succ k hpk ih =>
      intro hk
      obtain ⟨Y, hY⟩ := ih (Nat.lt_of_succ_lt hk)
      have e1 : H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))
          = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc) := rfl
      have e2 : H (⟨k + 1, hk⟩ : Fin (L + 1))
          = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ) := rfl
      rw [prodAux_succ H v k hk e1 e2, hY]
      refine ⟨Y * (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm)
        (v ⟨k, Nat.lt_of_succ_lt_succ hk⟩)), ?_⟩
      exact Matrix.mul_assoc (prodAux H v p hp) Y _

/-- **The general-`L` common (prefix) pivot at an optimal `v`.** At an optimal `v`
(`prod H v = B`, `B.rank = r`), there is a per-vertex family of injections
`ι : (s : Fin (L+1)) → Fin r → Fin (H s)` such that every prefix-product minor at the shared row set
`ι 0` is invertible: `((prodAux H v s).submatrix (ι 0) (ι s)).det ≠ 0` for all `s`. The general-`L`
lift of `exists_common_pivot_L2_at`; Cauchy–Binet-free (iterated rank squeeze). -/
theorem exists_common_pivot_gen (H : Fin (L + 1) → ℕ) (r : ℕ) (v : Params H)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hopt : prod H v = B) (hB : B.rank = r) :
    ∃ ι : (s : Fin (L + 1)) → Fin r → Fin (H s),
      (∀ s, Function.Injective (ι s)) ∧
      ∀ s : Fin (L + 1), ((prodAux H v s.1 s.2).submatrix (ι 0) (ι s)).det ≠ 0 := by
  classical
  have hpv : (prod H v).rank = r := by rw [hopt, hB]
  -- the full-product invertible minor fixes the shared row set `i0` (and a witness column set).
  obtain ⟨i0, cL, hi0, hcL, hfulldet⟩ :=
    Core.exists_square_minor (prod H v) (le_of_eq hpv.symm)
  -- the rank squeeze at each succ-vertex `t.succ`: a column set making the prefix minor invertible.
  have hsq : ∀ t : Fin L, ∃ js : Fin r → Fin (H t.succ),
      Function.Injective js ∧
        ((prodAux H v (t.succ).1 (t.succ).2).submatrix i0 js).det ≠ 0 := by
    intro t
    obtain ⟨Y, hY⟩ := prodAux_split_full H v (t.succ).1 (t.succ).2 L
      (Nat.lt_succ_iff.mp (t.succ).2) (Nat.lt_succ_self L)
    have hprod : (prod H v).submatrix i0 cL
        = (prodAux H v (t.succ).1 (t.succ).2).submatrix i0 id * Y.submatrix id cL := by
      change (prodAux H v L (Nat.lt_succ_self L)).submatrix i0 cL = _
      rw [hY, Matrix.submatrix_mul (prodAux H v (t.succ).1 (t.succ).2) Y i0 id cL
        Function.bijective_id]
    have hdet :
        ((prodAux H v (t.succ).1 (t.succ).2).submatrix i0 id * Y.submatrix id cL).det ≠ 0 := by
      rw [← hprod]; exact hfulldet
    have hrankprod :
        ((prodAux H v (t.succ).1 (t.succ).2).submatrix i0 id * Y.submatrix id cL).rank = r :=
      Core.rank_eq_of_det_ne_zero _ hdet
    have hle : r ≤ ((prodAux H v (t.succ).1 (t.succ).2).submatrix i0 id).rank := by
      have hml := Matrix.rank_mul_le_left
        ((prodAux H v (t.succ).1 (t.succ).2).submatrix i0 id) (Y.submatrix id cL)
      rwa [hrankprod] at hml
    obtain ⟨er, ec, her, hec, hminor⟩ :=
      Core.exists_square_minor ((prodAux H v (t.succ).1 (t.succ).2).submatrix i0 id) hle
    refine ⟨ec, hec, ?_⟩
    -- transport the det back to the row set `i0` via the row permutation `er`.
    have hbij : Function.Bijective er := (Finite.injective_iff_bijective).mp her
    set σ : Equiv.Perm (Fin r) := Equiv.ofBijective er hbij with hσ
    have hrw : ((prodAux H v (t.succ).1 (t.succ).2).submatrix i0 id).submatrix er ec
        = ((prodAux H v (t.succ).1 (t.succ).2).submatrix i0 ec).submatrix σ id := by
      ext i j
      simp only [Matrix.submatrix_apply, id_eq, hσ, Equiv.ofBijective_apply]
    have hne : (((prodAux H v (t.succ).1 (t.succ).2).submatrix i0 ec).submatrix σ id).det ≠ 0 := by
      rw [← hrw]; exact hminor
    rw [Matrix.det_permute σ ((prodAux H v (t.succ).1 (t.succ).2).submatrix i0 ec)] at hne
    exact right_ne_zero_of_mul hne
  -- assemble the family: `ι 0 = i0`, `ι (t.succ)` = the squeeze column set.
  refine ⟨Fin.cons i0 (fun t => (hsq t).choose), ?_, ?_⟩
  · intro s
    refine Fin.cases ?_ (fun t => ?_) s
    · simpa only [Fin.cons_zero] using hi0
    · simpa only [Fin.cons_succ] using (hsq t).choose_spec.1
  · intro s
    refine Fin.cases ?_ (fun t => ?_) s
    · -- `s = 0`: `prodAux H v 0 = 1`, so the minor is the identity.
      simp only [Fin.cons_zero]
      change ((1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ).submatrix i0 i0).det ≠ 0
      rw [Matrix.submatrix_one i0 hi0, Matrix.det_one]
      exact one_ne_zero
    · -- `s = t.succ`: the squeeze column set makes the prefix minor invertible.
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact (hsq t).choose_spec.2

end DLNFibre.DLN.RLCT
