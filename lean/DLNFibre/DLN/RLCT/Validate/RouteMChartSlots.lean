import DLNFibre.DLN.RLCT.Validate.RouteMChartIdxEquiv
import DLNFibre.DLN.RLCT.Validate.RouteMGenChain
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Matrix.Block

/-!
# `RouteMChartSlots` — the disjoint role-slot reader API (the shared decoder/factor foundation)

The shared coordinate-accessor foundation for the structured achiever-chart decoder + its factor CLEs
(the unblock for the item-3 map equality — see `thread.md` UPDATE + `codex/decoder-*`). The diagnosed
flaw was that `genBlkFlat` reads its block data via an arbitrary modular hash that COLLAPSES distinct
entries. The fix: read every block entry from a DISJOINT flat slot via the banked bijective
coordinatization `chartIdxEquiv : Fin (routeMAmbient M) ≃ ChartIdx M t`, with
`ChartIdx = Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k)`.

The per-boundary slot allocation (verified against `(3,3,3,3)`, `chartDim_eq_flatDim` ⟹ `∑ = N`):
* `schurDim k = t_k · M_{k+1}` holds the Schur frame at boundary `s = k+1` (`(t_s+r_s)(t_s+c_s) =
  t_{k}·M_{k+1}` after the `schurDim(s-1)↔frame(s)` shift); for `k = L−1` it holds the leaf residual.
* `liftDim k = (M_{k+1}−t_{k+1})·M_{k+2}` holds the lift `W_{k+1}`.

This module gives the `Fin`-product slot equivalences (`Fin (schurDim k) ≃ Fin (t_k) × Fin (M_{k+1})`
etc.) and the `chartIdxEquiv`-based scalar readers — disjoint by construction (distinct `ChartIdx`
indices ⟹ distinct flat coords). The structured decoder + the factor CLEs both read through these, so
the item-3 map equality is accessor lemmas, not a coordinate-collapse fight.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## The per-boundary slot ↔ matrix-index equivalences -/

/-- The Schur-block slot at boundary `k` as a `Fin (t_k) × Fin (M_{k+1})` matrix index
(`schurDim k = t_k · Wext (k+1)` via `finProdFinEquiv`). -/
def schurSlotEquiv (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (k : ℕ) :
    Fin (schurDim M t k) ≃ (Fin (t k) × Fin (Wext M (k + 1))) :=
  (finCongr (show schurDim M t k = t k * Wext M (k + 1) from rfl)).trans finProdFinEquiv.symm

/-- The lift slot at boundary `k` as a `Fin (M_{k+1} − t_{k+1}) × Fin (M_{k+2})` matrix index
(`liftDim k = (Wext (k+1) − t (k+1)) · Wext (k+2)` when `k+1 < L`). -/
def liftSlotEquiv (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ) (k : ℕ) (hk : k + 1 < L) :
    Fin (liftDim M t k) ≃ (Fin (Wext M (k + 1) - t (k + 1)) × Fin (Wext M (k + 2))) :=
  (finCongr (show liftDim M t k = (Wext M (k + 1) - t (k + 1)) * Wext M (k + 2) by
    rw [liftDim, if_pos hk])).trans finProdFinEquiv.symm

/-! ## The disjoint scalar readers (via `chartIdxEquiv`) -/

/-- Read the flat coordinate at the Schur-block slot `(i, j)` of boundary `k`. Disjoint across
`(k, i, j)` by `chartIdxEquiv`'s injectivity. -/
noncomputable def readSchur (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    (x : Fin (routeMAmbient M) → ℝ) (k : Fin L) (i : Fin (t k.val)) (j : Fin (Wext M (k.val + 1))) :
    ℝ :=
  x ((chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inl ((schurSlotEquiv M t k.val).symm (i, j))⟩)

/-- Read the flat coordinate at the lift slot `(i, j)` of boundary `k` (`k+1 < L`). Disjoint across
`(k, i, j)`. -/
noncomputable def readLift (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    (x : Fin (routeMAmbient M) → ℝ) (k : Fin L) (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - t (k.val + 1))) (j : Fin (Wext M (k.val + 2))) : ℝ :=
  x ((chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inr ((liftSlotEquiv M t k.val hk).symm (i, j))⟩)

/-! ## Disjointness: distinct `(boundary, role, entry)` triples read distinct flat coords -/

/-- The Schur reader's flat index is injective in `(k, i, j)` — distinct Schur entries read distinct
flat coords (the disjointness the modular hash lacked). -/
theorem readSchur_index_injective (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    {k k' : Fin L} {i : Fin (t k.val)} {j : Fin (Wext M (k.val + 1))}
    {i' : Fin (t k'.val)} {j' : Fin (Wext M (k'.val + 1))}
    (h : (chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inl ((schurSlotEquiv M t k.val).symm (i, j))⟩
       = (chartIdxEquiv M t h0 hc hL).symm ⟨k', Sum.inl ((schurSlotEquiv M t k'.val).symm (i', j'))⟩) :
    (⟨k, Sum.inl ((schurSlotEquiv M t k.val).symm (i, j))⟩ : ChartIdx M t)
      = ⟨k', Sum.inl ((schurSlotEquiv M t k'.val).symm (i', j'))⟩ :=
  (chartIdxEquiv M t h0 hc hL).symm.injective h

/-- A Schur slot and a lift slot at the same boundary read DISTINCT flat coords (`Sum.inl ≠ Sum.inr`
under the injective `chartIdxEquiv`). -/
theorem readSchur_ne_readLift_index (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ p, t (p + 1) ≤ (Wext M) (p + 1)) (hL : 0 < L)
    (k : Fin L) (a : Fin (schurDim M t k.val)) (b : Fin (liftDim M t k.val)) :
    (chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inl a⟩
      ≠ (chartIdxEquiv M t h0 hc hL).symm ⟨k, Sum.inr b⟩ := by
  intro h
  have hsig := (chartIdxEquiv M t h0 hc hL).symm.injective h
  -- equal sigmas at the SAME fst `k` ⟹ equal snd (a `Sum`), but `inl ≠ inr`
  have hsnd : (Sum.inl a : Fin (schurDim M t k.val) ⊕ Fin (liftDim M t k.val)) = Sum.inr b := by
    simpa using (Sigma.mk.inj_iff.mp hsig).2
  exact absurd hsnd (by simp)

/-! ## The derived `Bmat` block-stack constructor (the Schur-frame kept part `[K ; X·K]`)

The structured decoder's `Bmat s` is the kept part of the Schur frame: top block `K_s`
(`Text(s+1) × Text(s+1)`), bottom block `X_s · K_s` (`r_s × Text(s+1)`), stacked to
`Text s × Text(s+1)` rows under the descent `Text(s+1) ≤ Text s` (`r_s = Text s − Text(s+1)`). The
validated dependent-width row-stack the next-tide `genBlkFlatStruct` consumes. -/

/-- **The Schur-frame kept block** `Bmat s = [K ; X·K]` (`Text s × Text(s+1)`), the top `K` over the
first `Text(s+1)` rows, the bottom `X·K` over the residual `r_s = Text s − Text(s+1)` rows
(`finSumFinEquiv` row split + a `Text(s+1) + r_s = Text s` reindex; needs the descent
`Text(s+1) ≤ Text s`). -/
noncomputable def bmatStack {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (k : ℕ)
    (hdesc : Text M t (k + 1) ≤ Text M t k)
    (K : Matrix (Fin (Text M t (k + 1))) (Fin (Text M t (k + 1))) ℝ)
    (X : Matrix (Fin (Text M t k - Text M t (k + 1))) (Fin (Text M t (k + 1))) ℝ) :
    Matrix (Fin (Text M t k)) (Fin (Text M t (k + 1))) ℝ :=
  Matrix.reindex
    (finCongr (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega))
    (Equiv.refl _)
    (Matrix.of (fun (i : Fin (Text M t (k + 1) + (Text M t k - Text M t (k + 1))))
        (j : Fin (Text M t (k + 1))) =>
      Sum.elim (fun a => K a j) (fun b => (X * K) b j) (finSumFinEquiv.symm i)))

/-- The top `Text(s+1)` rows of `bmatStack` are `K` (the `finSumFinEquiv` `castAdd` block). -/
theorem bmatStack_top {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (k : ℕ)
    (hdesc : Text M t (k + 1) ≤ Text M t k)
    (K : Matrix (Fin (Text M t (k + 1))) (Fin (Text M t (k + 1))) ℝ)
    (X : Matrix (Fin (Text M t k - Text M t (k + 1))) (Fin (Text M t (k + 1))) ℝ)
    (a : Fin (Text M t (k + 1))) (j : Fin (Text M t (k + 1))) :
    bmatStack M t k hdesc K X
        (Fin.cast (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega)
          (Fin.castAdd _ a)) j
      = K a j := by
  rw [bmatStack, Matrix.reindex_apply]
  simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_symm,
    Equiv.refl_apply, Matrix.of_apply]
  rw [show (Fin.cast (show Text M t k = Text M t (k + 1) + (Text M t k - Text M t (k + 1)) by omega)
        (Fin.cast (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega)
          (Fin.castAdd _ a)))
        = Fin.castAdd (Text M t k - Text M t (k + 1)) a from by apply Fin.ext; simp,
    finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]

/-- The bottom `r_s` rows of `bmatStack` are `X·K` (the `finSumFinEquiv` `natAdd` block). -/
theorem bmatStack_bot {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (k : ℕ)
    (hdesc : Text M t (k + 1) ≤ Text M t k)
    (K : Matrix (Fin (Text M t (k + 1))) (Fin (Text M t (k + 1))) ℝ)
    (X : Matrix (Fin (Text M t k - Text M t (k + 1))) (Fin (Text M t (k + 1))) ℝ)
    (b : Fin (Text M t k - Text M t (k + 1))) (j : Fin (Text M t (k + 1))) :
    bmatStack M t k hdesc K X
        (Fin.cast (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega)
          (Fin.natAdd _ b)) j
      = (X * K) b j := by
  rw [bmatStack, Matrix.reindex_apply]
  simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_symm,
    Equiv.refl_apply, Matrix.of_apply]
  rw [show (Fin.cast (show Text M t k = Text M t (k + 1) + (Text M t k - Text M t (k + 1)) by omega)
        (Fin.cast (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega)
          (Fin.natAdd _ b)))
        = Fin.natAdd (Text M t (k + 1)) b from by apply Fin.ext; simp,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

/-! ## The Schur-frame slot K/X/N/E sub-split

The frame slot at GenBlk boundary `s` (size `Text s · Wext s`) sub-splits into the Schur roles
`K` (`Text(s+1)²`), `X` (`r_s·Text(s+1)`), `N` (`Text(s+1)·c_s`), `E` (`r_s·c_s`), where
`r_s = Text s − Text(s+1)`, `c_s = Wext s − Text(s+1)`. The `(((K + X) + N) + E) = Text s · Wext s`
identity is the banked `roleSquare_eq`; the split equiv nests `finSumFinEquiv.symm` left-to-right. -/

/-- **The Schur-frame slot K/X/N/E sub-split equivalence** — `Fin (Text s · Wext s) ≃ (((K ⊕ X) ⊕ N)
⊕ E)` at the role-block sizes, via `roleSquare_eq` + left-nested `finSumFinEquiv.symm`. The decoder's
per-frame role accessor base (`K`, `X`, `N`, `E` blocks of the Schur frame at boundary `s`). -/
def frameSplitEquiv {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) :
    Fin (Text M t s * Wext M s) ≃
      (((Fin (Text M t (s + 1) * Text M t (s + 1)) ⊕
         Fin ((Text M t s - Text M t (s + 1)) * Text M t (s + 1))) ⊕
        Fin (Text M t (s + 1) * (Wext M s - Text M t (s + 1)))) ⊕
       Fin ((Text M t s - Text M t (s + 1)) * (Wext M s - Text M t (s + 1)))) :=
  (finCongr (roleSquare_eq h1 h2).symm).trans
    ((finSumFinEquiv.symm).trans
      (((finSumFinEquiv.symm).trans
        (((finSumFinEquiv.symm).trans (Equiv.refl _)).sumCongr (Equiv.refl _))).sumCongr
          (Equiv.refl _)))

/-! ## The derived `Rmat` block-pad constructor (the Schur-frame `u`-carrier `[[0,0],[0,E]]`)

The structured decoder's `Rmat s` is the `u`-carrying residual of the Schur frame: the `E_s`
(`r_s × c_s`) block placed BOTTOM-RIGHT of a `Text s × Wext s` zero matrix, so
`C_s = Bmat_s·chainQ(N_s) + u·Rmat_s = [[K, KN],[XK, XKN + uE]]` (the Schur frame). A
`Matrix.fromBlocks 0 0 0 E` padded by `finSumFinEquiv` row/col reindexes. -/

/-- **The Schur-frame `u`-carrier block** `Rmat s = [[0,0],[0,E]]` (`Text s × Wext s`), the `E_s` block
(`r_s × c_s`) in the bottom-right, zeros elsewhere (`Matrix.fromBlocks 0 0 0 E` + `finSumFinEquiv`
row/col reindex to `Text s × Wext s`). -/
noncomputable def rmatPad {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ) :
    Matrix (Fin (Text M t s)) (Fin (Wext M s)) ℝ :=
  Matrix.reindex
    (finSumFinEquiv.trans
      (finCongr (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)))
    (finSumFinEquiv.trans
      (finCongr (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)))
    (Matrix.fromBlocks (0 : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ) 0 0 E)

end DLNFibre.DLN.RLCT
