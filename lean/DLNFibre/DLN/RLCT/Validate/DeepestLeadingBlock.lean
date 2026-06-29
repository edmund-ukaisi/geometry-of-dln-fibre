import DLNFibre.DLN.RLCT.Validate.DeepestFrame
import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeel

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestLeadingBlock` — KC1: the deepest point's layer-0 leading block

The alignment-conditional fact the gauge producer's block-triangular endpoint frames need (the
`[Invertible A11]` precondition of `Core.Matrix.blockLower_left_normalizer`, consumed at
`DeepestGaugeConstruction`'s 2915 obligation): **at a row-aligned target `B` (its top `r` rows full
rank — `htop`), the deepest point's layer-0 has an invertible leading `r×r` block.**

This is **htop-CONDITIONAL**, not general-`B`: the Q1 witness `B = [[0,0],[1,0]]` (rank 1, `Im(B) =
span(e₂)`) has layer-0 leading block `[0]` singular for EVERY deepest point — the row-WLOG
(`rlct_infimum_rowPerm_eq`, the KC1 step-1 dual of the banked colPerm) supplies `htop` at the headline
(`kc1-route1-adjudication.md`). The producer's docstring "always achievable" (`a11_check.py`) is
POST-row-WLOG achievability — consistent with this `htop` gate.

PROOF (route B, standalone, downstream of `deepestPoint` — NO `IsDeepLayers`/`deepestPoint_exists`
edit, NO `U,V`): `deepestPoint_isDeep.1` gives `prod = B`; `prod_front_peel` gives `B = layer0 ·
reindex(rest)`; `deepestPoint_layer0_cols_vanish` (the banked conjunct-4, `2 ≤ L`) gives layer-0's
tail columns zero, so `layer0 · rest = (leading r×r block) · (top-`r` rows of rest)` on the top `r`
rows. Hence `top-r-rows(B) = (leading block) · (top-r-rows of rest)`, and with `htop`
(`rank (top-r-rows B) = r`): `r = rank(top-r-rows B) ≤ rank(leading block) ≤ r` (it is `r×r`), so the
leading block is full rank, hence invertible (square full-rank over `ℝ`).
-/

open Matrix
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **A square full-rank matrix over `ℝ` is a unit.** `rank A = Fintype.card n` ⟹ `A.mulVecLin`
surjective ⟹ (finite-dim) bijective ⟹ `A` invertible. The reverse of `Matrix.rank_of_isUnit`. -/
private theorem isUnit_of_rank_eq_card {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A.rank = n) : IsUnit A := by
  -- `rank A = n` ⟹ `range A.toLin'` has full finrank ⟹ `= ⊤` ⟹ `A.toLin'` a unit ⟹ `A` a unit.
  rw [← Matrix.isUnit_toLin'_iff, LinearMap.isUnit_iff_range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hrange : Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = A.rank := rfl
  rw [hrange, h, Module.finrank_fin_fun]

/-- **A matrix with zero tail columns factors its product through the leading block.** If `A : Fin r ×
Fin n` has its columns `≥ r` zero, then `A * X = (leading `r×r` block of `A`) · (top-`r` rows of `X`)`
— the zero tail columns kill the bottom block of `X` in the middle sum. (Sum-split via `Finset.map
(Fin.castLEEmb)` + `Finset.sum_subset`, opaque-width-robust — no block API, no `Fin n` split by an
opaque equality.) -/
private theorem zeroTail_mul_eq_leading_mul_top
    {r n c : ℕ} (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin n) ℝ) (X : Matrix (Fin n) (Fin c) ℝ)
    (hA_tail : ∀ i (j : Fin n), r ≤ (j : ℕ) → A i j = 0) :
    A * X =
      (A.submatrix (id : Fin r → Fin r) (Fin.castLE hrn)) *
        (X.submatrix (Fin.castLE hrn) (id : Fin c → Fin c)) := by
  classical
  ext i k
  let f : Fin n → ℝ := fun j => A i j * X j k
  change (∑ j : Fin n, f j) = ∑ j : Fin r, f (Fin.castLE hrn j)
  let S : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hrn)
  have hsmall : (∑ j : Fin r, f (Fin.castLE hrn j)) = ∑ j ∈ S, f j := by
    simpa [S] using
      (Finset.sum_map (s := (Finset.univ : Finset (Fin r))) (Fin.castLEEmb hrn) (g := f)).symm
  have hbig : (∑ j : Fin n, f j) = ∑ j ∈ S, f j := by
    refine (Finset.sum_subset (s₁ := S) (s₂ := Finset.univ) (f := f)
      (by intro j _; exact Finset.mem_univ j) ?_).symm
    intro j _ hjnot
    have hjge : r ≤ (j : ℕ) := by
      by_contra hjnge
      have hjlt : (j : ℕ) < r := Nat.lt_of_not_ge hjnge
      apply hjnot
      change j ∈ (Finset.univ : Finset (Fin r)).map (Fin.castLEEmb hrn)
      exact Finset.mem_map.mpr ⟨⟨(j : ℕ), hjlt⟩, by simp, by ext; simp⟩
    simp [f, hA_tail i j hjge]
  exact hbig.trans hsmall.symm

/-- **KC1 (route B): the deepest point's layer-0 leading `r×r` block is invertible, at a row-aligned
`B`.** Given `htop : (top `r` rows of `B`) has rank `r`` (supplied at the headline by the row-WLOG),
the deepest point's first layer's leading `r×r` block is a unit — the `[Invertible A11]` the
block-triangular endpoint normalizers need. -/
theorem deepestPoint_leadingBlock_isUnit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r) :
    IsUnit ((deepestPoint H r B hB hr hL (⟨0, by omega⟩ : Fin L)).submatrix
      (Fin.castLE (hr (⟨0, by omega⟩ : Fin L).castSucc) : Fin r → Fin (H (⟨0, by omega⟩ : Fin L).castSucc))
      (Fin.castLE (hr (⟨0, by omega⟩ : Fin L).succ) : Fin r → Fin (H (⟨0, by omega⟩ : Fin L).succ))) := by
  classical
  -- Reshape `L = L'+1` (from `1 ≤ L`) so `H : Fin (L'+1+1) → ℕ` fits `prod_front_peel`.
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  set s0 : Fin (L' + 1) := ⟨0, by omega⟩ with hs0
  have hs0eq : s0 = (0 : Fin (L' + 1)) := rfl
  -- The deepest point + its fibre membership `prod = B`.
  set w := deepestPoint H r B hB hr hL with hw
  have hfib : prod H w = B := (deepestPoint_isDeep H r B hB hr hL).1
  -- layer-0 (the leftmost factor) and its leading `r×r` block `LB`.
  set layer0 : Matrix (Fin (H s0.castSucc)) (Fin (H s0.succ)) ℝ := w s0 with hlayer0
  set LB : Matrix (Fin r) (Fin r) ℝ :=
    layer0.submatrix (Fin.castLE (hr s0.castSucc) : Fin r → Fin (H s0.castSucc))
      (Fin.castLE (hr s0.succ) : Fin r → Fin (H s0.succ)) with hLB
  -- It suffices to show `LB.rank = r` (square full-rank ⟹ unit).
  suffices hLBrank : LB.rank = r by exact isUnit_of_rank_eq_card LB hLBrank
  -- `front_peel`: `prod H w = w 0 · reindex(prod (Mtail H)(Atail H w))`. `w 0 = layer0` (defeq).
  have emid : Mtail H (0 : Fin (L' + 1)) = H ((0 : Fin (L' + 1)).succ) := rfl
  have ecol : Mtail H (Fin.last L') = H (Fin.last (L' + 1)) := rfl
  have hpeel := prod_front_peel H w emid ecol
  -- `top-r-rows(B) = (top-r-rows layer0)·(reindex rest)`, then zero-tail collapse ⟹ `= LB · Y`.
  set rest := Matrix.reindex (finCongr emid) (finCongr ecol)
    (prod (Mtail H) (Atail H w)) with hrest
  -- `htail`: layer0's tail columns vanish (`deepestPoint_layer0_cols_vanish`, banked conjunct-4).
  have htail : ∀ i (j : Fin (H s0.succ)), r ≤ (j : ℕ) → layer0 i j = 0 := by
    intro i j hj
    exact deepestPoint_layer0_cols_vanish H r B hB hr hL s0 hL2 (by simp [hs0]) i j hj
  -- The factorization `top-r-rows(B) = LB · Y`.
  have htop0 : r ≤ H s0.castSucc := hr s0.castSucc
  set Y : Matrix (Fin r) (Fin (H (Fin.last (L' + 1)))) ℝ :=
    rest.submatrix (Fin.castLE (hr s0.succ) : Fin r → Fin (H s0.succ))
      (id : Fin (H (Fin.last (L' + 1))) → Fin (H (Fin.last (L' + 1)))) with hY
  -- The matrix-assembly identity `top-r-rows(B) = LB · Y`, from `B = w0·rest` (front-peel,
  -- `hpeel`) + `submatrix_mul` (left rows through, `hstep`) + `zeroTail_mul_eq_leading_mul_top`
  -- (the zero-tail collapse). The dependent-width `submatrix_submatrix` fold is dodged entrywise
  -- (`hLBeq` via `Matrix.ext` + `submatrix_apply`, `w 0` defeq `w s0 = layer0`; `hYeq` is `rfl`).
  have hfactor : B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last (L' + 1))) → Fin (H (Fin.last (L' + 1)))) = LB * Y := by
    -- Work with `w 0 * rest` (HMul already resolved by `hpeel`), restrict top rows, collapse zero tail.
    have hBpeel : B = (w 0) * rest := by rw [← hfib]; exact hpeel
    have htail0 : ∀ i (j : Fin (H ((0 : Fin (L' + 1)).succ))), r ≤ (j : ℕ) → (w 0) i j = 0 :=
      fun i j hj => htail i j hj
    -- `top-r-rows(B) = (top-r-rows w0) · rest` (submatrix_mul, left rows through — GREEN as `hstep`).
    have hstep : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
          (id : Fin (H (Fin.last (L' + 1))) → Fin (H (Fin.last (L' + 1)))))
        = ((w 0).submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
            (id : Fin (H ((0 : Fin (L' + 1)).succ)) → Fin (H ((0 : Fin (L' + 1)).succ)))) * rest := by
      rw [hBpeel]
      exact Matrix.submatrix_mul (w 0) rest (Fin.castLE (hr 0))
        (id : Fin (H ((0 : Fin (L' + 1)).succ)) → Fin (H ((0 : Fin (L' + 1)).succ)))
        (id : Fin (H (Fin.last (L' + 1))) → Fin (H (Fin.last (L' + 1)))) Function.bijective_id
    -- The top-row slice `A'` of `w 0`, and the zero-tail collapse on `A' * rest`.
    set A' : Matrix (Fin r) (Fin (H ((0 : Fin (L' + 1)).succ))) ℝ :=
      (w 0).submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H ((0 : Fin (L' + 1)).succ)) → Fin (H ((0 : Fin (L' + 1)).succ))) with hA'
    have hrn : r ≤ H ((0 : Fin (L' + 1)).succ) := hr ((0 : Fin (L' + 1)).succ)
    -- `A'` inherits `w 0`'s zero tail columns (the submatrix selects all columns via `id`).
    have hA'_tail : ∀ i (j : Fin (H ((0 : Fin (L' + 1)).succ))), r ≤ (j : ℕ) → A' i j = 0 := by
      intro i j hj
      simp only [hA', Matrix.submatrix_apply, id_eq]
      exact htail0 (Fin.castLE (hr 0) i) j hj
    -- Zero-tail collapse: `A' * rest = (leading block of A') · (top-r rows of rest)`.
    have hcollapse := zeroTail_mul_eq_leading_mul_top (r := r)
      (n := H ((0 : Fin (L' + 1)).succ)) (c := H (Fin.last (L' + 1))) hrn A' rest hA'_tail
    -- `top-r-rows(B) = A' * rest` (hstep) → collapse → fold the two slices to `LB` / `Y`.
    rw [hstep, hcollapse]
    -- The right slice is `Y` definitionally (same `submatrix` shape, `s0.succ` defeq `(0:Fin _).succ`).
    have hYeq : rest.submatrix (Fin.castLE hrn) (id : Fin (H (Fin.last (L' + 1))) → _) = Y := rfl
    -- The left slice folds to `LB`, entrywise (dodge `submatrix_submatrix`; `w 0` defeq `w s0 = layer0`).
    have hLBeq : A'.submatrix (id : Fin r → Fin r) (Fin.castLE hrn) = LB := by
      apply Matrix.ext
      intro i j
      simp only [hA', hLB, hlayer0, Matrix.submatrix_apply, id_eq]
      rfl
    rw [hYeq, hLBeq]
  -- Rank-squeeze: `r = rank(top-r-rows B) ≤ rank LB ≤ r`.
  have hge : r ≤ LB.rank := by
    calc r = (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
            (id : Fin (H (Fin.last (L' + 1))) → Fin (H (Fin.last (L' + 1))))).rank := htop.symm
      _ = (LB * Y).rank := by rw [hfactor]
      _ ≤ LB.rank := Matrix.rank_mul_le_left LB Y
  have hle : LB.rank ≤ r := Matrix.rank_le_height LB
  exact le_antisymm hle hge

end DLNFibre.DLN.RLCT
