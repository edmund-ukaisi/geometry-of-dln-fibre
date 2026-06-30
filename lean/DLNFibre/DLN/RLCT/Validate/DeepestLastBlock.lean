import DLNFibre.DLN.RLCT.Validate.DeepestFrame
import DLNFibre.DLN.RLCT.Validate.DeepestBlockDecomp

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestLastBlock` — KC2: the deepest point's last-layer leading block

The COLUMN-side dual of `DeepestLeadingBlock` (KC1): at a column-aligned target `B` (its front `r`
columns full rank — `hcolfront`), the deepest point's LAST layer has an invertible (full-rank) top-left
`r×r` block. This is the `hfront` precursor that the front-pivot frame builder
`exists_frontPivotFrame_lastBlock_isUnit` (`DeepestPivotFrame`) consumes to return `J = frontEmbed`
DETERMINISTICALLY — discharging the `hJfront` hypothesis of the L=2 value lemma without the arbitrary
`exists_pivot_cols_of_rank` choice (genm-44l2).

PROOF (the column-dual of `DeepestLeadingBlock`'s route B, standalone — NO `deepestPoint_exists` edit):
`deepestPoint_isDeep.1` gives `prod = B`; `prod_eq_prodAux_mul_last` (the banked back-peel) gives
`B = G · A_last` with `G = prodAux (first L−1)` and `A_last` the last layer (recast);
`deepestPoint_layerLast_rows_vanish` (the banked last-clause, `2 ≤ L`) gives `A_last`'s tail ROWS zero,
so the front `r` columns of `A_last` are `[V_front; 0]` (`V` = its top `r` rows), and
`B_front = G · A_last_front = (front r cols of G) · V_front` on the front columns. Hence with `hcolfront`
(`rank (front r cols of B) = r`): `r = rank(front-cols B) ≤ rank V_front ≤ r`, so the top-left `r×r`
block `V_front` of `A_last` is full rank.

The column-WLOG (`headline_frontRowColPivot_exists`, sorry-free) supplies `hcolfront` at the headline ⨅
(the front-`r`-COLUMNS rank fact), just as the row-WLOG supplies `htop` for `DeepestLeadingBlock`.
-/

open Matrix
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **A square full-rank matrix over `ℝ` is a unit** (local copy; cf. `DeepestLeadingBlock`). -/
private theorem isUnit_of_rank_eq_card' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A.rank = n) : IsUnit A := by
  rw [← Matrix.isUnit_toLin'_iff, LinearMap.isUnit_iff_range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hrange : Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = A.rank := rfl
  rw [hrange, h, Module.finrank_fin_fun]

/-- **A matrix with zero tail ROWS factors its product through the leading block** (the COLUMN-dual of
`DeepestLeadingBlock.zeroTail_mul_eq_leading_mul_top`, on the RIGHT factor). If `A_last : Fin n × Fin c`
has its rows `≥ r` zero, then `X · A_last = (left-`r` cols of `X`) · (top-`r` rows of `A_last`)` — the
zero tail rows kill the bottom block of `X` in the middle sum. -/
private theorem mul_zeroTailRows_eq_left_mul_top
    {m n c r : ℕ} (hrn : r ≤ n)
    (X : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin c) ℝ)
    (hA_tail : ∀ (i : Fin n) k, r ≤ (i : ℕ) → A i k = 0) :
    X * A =
      (X.submatrix (id : Fin m → Fin m) (Fin.castLE hrn)) *
        (A.submatrix (Fin.castLE hrn) (id : Fin c → Fin c)) := by
  classical
  ext i k
  let f : Fin n → ℝ := fun j => X i j * A j k
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
    simp [f, hA_tail j k hjge]
  exact hbig.trans hsmall.symm

/-- **KC2 (the column-dual): the deepest point's last-layer top-left `r×r` block is full rank, at a
column-aligned `B`.** Given `hcolfront : (front `r` columns of `B`) has rank `r`` (supplied at the
headline by the column-WLOG), the deepest point's LAST layer's top-left `r×r` block has rank `r` — the
`hfront` precursor that `exists_frontPivotFrame_lastBlock_isUnit` consumes to build the front-pivot frame
(`J = frontEmbed`) deterministically. -/
theorem deepestPoint_lastBlock_front_rank (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last L)) : Fin r → Fin (H (Fin.last L)))).rank = r) :
    ((deepestPoint H r B hB hr hL (lastLayer hL)).submatrix
        (Fin.castLE (hr (lastLayer hL).castSucc) : Fin r → Fin (H (lastLayer hL).castSucc))
        (Fin.castLE (hr (lastLayer hL).succ) : Fin r → Fin (H (lastLayer hL).succ))).rank = r := by
  classical
  -- Reshape `L = L'+1` so `H : Fin (L'+1+1) → ℕ` fits `prod_eq_prodAux_mul_last`.
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  -- The deepest point + fibre membership `prod = B`.
  set w := deepestPoint H r B hB hr hL with hw
  have hfib : prod H w = B := (deepestPoint_isDeep H r B hB hr hL).1
  -- The last layer index `sL = lastLayer hL = ⟨L', _⟩ : Fin (L'+1)`.
  set sL : Fin (L' + 1) := lastLayer hL with hsL
  have hsLval : (sL : ℕ) = L' := by simp [hsL, lastLayer]
  -- The last layer `A_last := w sL` and its top-left `r×r` block `LB`.
  set A_last : Matrix (Fin (H sL.castSucc)) (Fin (H sL.succ)) ℝ := w sL with hAlast
  set LB : Matrix (Fin r) (Fin r) ℝ :=
    A_last.submatrix (Fin.castLE (hr sL.castSucc) : Fin r → Fin (H sL.castSucc))
      (Fin.castLE (hr sL.succ) : Fin r → Fin (H sL.succ)) with hLB
  -- It suffices to show `LB.rank = r` (the goal IS `LB.rank = r`, defeq).
  show LB.rank = r
  -- The back-peel `prod H w = G · A_last'` with `G = prodAux (first L')` and `A_last'` the recast
  -- last layer. The two `finCongr` casts are identity-on-value (`e1`/`e2` are `rfl`).
  have e1 : H (⟨L', Nat.lt_of_succ_lt (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1 + 1))
      = H ((⟨L', Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1)).castSucc) := rfl
  have e2 : H (⟨L' + 1, Nat.lt_succ_self (L' + 1)⟩ : Fin (L' + 1 + 1))
      = H ((⟨L', Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1)).succ) := rfl
  have hpeel := prod_eq_prodAux_mul_last (m := L') H w e1 e2
  set G : Matrix (Fin (H 0)) (Fin (H (⟨L', Nat.lt_of_succ_lt (Nat.lt_succ_self (L' + 1))⟩ :
      Fin (L' + 1 + 1)))) ℝ :=
    prodAux H w L' (Nat.lt_of_succ_lt (Nat.lt_succ_self (L' + 1))) with hG
  -- `⟨L', _⟩ : Fin (L'+1) = sL` (both val `L'`), so `w ⟨L',_⟩ = A_last` and the layer in `hpeel` IS
  -- `A_last` (recast). `Arec := reindex (finCongr e1.symm) (finCongr e2.symm) (w ⟨L',_⟩)`.
  set Arec : Matrix (Fin (H (⟨L', Nat.lt_of_succ_lt (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1 + 1))))
      (Fin (H (⟨L' + 1, Nat.lt_succ_self (L' + 1)⟩ : Fin (L' + 1 + 1)))) ℝ :=
    Matrix.reindex (finCongr e1.symm) (finCongr e2.symm)
      (w (⟨L', Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1))) with hArec
  -- `B = G · Arec`.
  have hBpeel : B = G * Arec := by rw [← hfib]; exact hpeel
  -- `Arec`'s tail ROWS vanish (inherited from `A_last`'s, through the value-identity reindex).
  have hAtail : ∀ (i : Fin (H (⟨L', Nat.lt_of_succ_lt (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1 + 1))))
      k, r ≤ (i : ℕ) → Arec i k = 0 := by
    intro i k hi
    simp only [hArec, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply]
    -- the reindex is a value-cast; apply the last-layer row-vanishing at `s = ⟨L',_⟩` DIRECTLY (no
    -- rewrite under `w`): `(⟨L',_⟩ : ℕ) + 1 = L' + 1 = L`, and the cast preserves `i`'s value.
    exact deepestPoint_layerLast_rows_vanish H r B hB hr hL
      (⟨L', Nat.lt_of_succ_lt_succ (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1)) hL2 rfl
      (Fin.cast (by rw [e1]) i) (Fin.cast (by rw [e2]) k) (by simpa [Fin.coe_cast] using hi)
  -- The width-`r` columns of `B` are `castLE`. Front-column factorization `B_front = G · Arec_front`.
  set hrn : r ≤ H (⟨L', Nat.lt_of_succ_lt (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1 + 1)) :=
    hr _ with hrn_def
  -- `B_front = G_left · (top-r-rows of Arec_front) = G_left · LB'` via the zero-tail-rows collapse.
  -- First: `B.submatrix id castLE = (G * Arec).submatrix id castLE = G * (Arec.submatrix id castLE)`.
  have hstep : B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last (L' + 1))) : Fin r → Fin (H (Fin.last (L' + 1))))
      = G * (Arec.submatrix (id : Fin _ → Fin _)
          (Fin.castLE (hr (Fin.last (L' + 1))) : Fin r → Fin (H (Fin.last (L' + 1))))) := by
    rw [hBpeel]
    exact Matrix.submatrix_mul G Arec (id : Fin (H 0) → Fin (H 0))
      (id : Fin (H (⟨L', Nat.lt_of_succ_lt (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1 + 1)))
        → Fin (H (⟨L', Nat.lt_of_succ_lt (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1 + 1))))
      (Fin.castLE (hr (Fin.last (L' + 1)))) Function.bijective_id
  -- Zero-tail-ROWS collapse on the MIDDLE index: `G * Arecf = G_left · (top-r rows of Arecf)`.
  set Arecf : Matrix (Fin (H (⟨L', Nat.lt_of_succ_lt (Nat.lt_succ_self (L' + 1))⟩ : Fin (L' + 1 + 1))))
      (Fin r) ℝ :=
    Arec.submatrix (id : Fin _ → Fin _)
      (Fin.castLE (hr (Fin.last (L' + 1))) : Fin r → Fin (H (Fin.last (L' + 1)))) with hArecf
  have hArecf_tail : ∀ (i : Fin (H (⟨L', Nat.lt_of_succ_lt (Nat.lt_succ_self (L' + 1))⟩ :
        Fin (L' + 1 + 1)))) (k : Fin r), r ≤ (i : ℕ) → Arecf i k = 0 := by
    intro i k hi; simp only [hArecf, Matrix.submatrix_apply, id_eq]; exact hAtail i _ hi
  have hcollapse := mul_zeroTailRows_eq_left_mul_top (r := r) hrn G Arecf hArecf_tail
  -- The left slice `G_left` and the top-`r`-rows slice `LB' := top-r-rows of Arecf` (= LB up to recast).
  set Gl : Matrix (Fin (H 0)) (Fin r) ℝ :=
    G.submatrix (id : Fin (H 0) → Fin (H 0)) (Fin.castLE hrn) with hGl
  set LB' : Matrix (Fin r) (Fin r) ℝ :=
    Arecf.submatrix (Fin.castLE hrn) (id : Fin r → Fin r) with hLB'
  -- `B_front = Gl * LB'`.
  have hfactor : B.submatrix (id : Fin (H 0) → Fin (H 0))
      (Fin.castLE (hr (Fin.last (L' + 1))) : Fin r → Fin (H (Fin.last (L' + 1)))) = Gl * LB' := by
    rw [hstep, hcollapse]
  -- `LB' = LB` (the top-r-rows-front-cols of Arec = top-left block of A_last; both value-casts).
  have hLB'eq : LB' = LB := by
    apply Matrix.ext; intro i j
    simp only [hLB', hArecf, hArec, hLB, hAlast, Matrix.submatrix_apply, id_eq,
      Matrix.reindex_apply, finCongr_symm, finCongr_apply]
    -- `sL = ⟨L',_⟩` defeq (`lastLayer hL = ⟨L-1,_⟩ = ⟨L',_⟩`), so `w sL = w ⟨L',_⟩`; the value-casts
    -- on the indices match by `Fin.ext`. No rewrite under `w` (avoids the dependent motive).
    congr 1 <;> · apply Fin.ext; simp [Fin.coe_cast]
  rw [hLB'eq] at hfactor
  -- Rank-squeeze: `r = rank(front cols B) ≤ rank LB ≤ r`.
  have hge : r ≤ LB.rank := by
    calc r = (B.submatrix (id : Fin (H 0) → Fin (H 0))
            (Fin.castLE (hr (Fin.last (L' + 1))) : Fin r → Fin (H (Fin.last (L' + 1))))).rank :=
          hcolfront.symm
      _ = (Gl * LB).rank := by rw [hfactor]
      _ ≤ LB.rank := Matrix.rank_mul_le_right Gl LB
  have hle : LB.rank ≤ r := Matrix.rank_le_width LB
  exact le_antisymm hle hge

end DLNFibre.DLN.RLCT
