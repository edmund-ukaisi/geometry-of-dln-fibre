import DLNFibre.DLN.RLCT.Validate.RouteMAchieverVvalPoly

/-!
# `RouteMAchieverWitnessInterior` — the INTERIOR-drop pivot-survival witness

The genuinely-remaining input for the rate-side `NodeAchieverChart.Ubound` on the INTERIOR class
(285/351 `M` on the cert's grid): `∃ w, achieverUfun M hL hN w ≠ 0`. Combined with the banked
`achieverUbound` (`RouteMAchieverVvalPoly`), this closes the a.e.-positivity for interior-drop `M`.

## The class
INTERIOR-drop `M` (cert `certificate-genM-witness-v2.md` §2): some chain boundary `p ∈ [1, L−1]`
drops both the row rank (`Text(p+1) < Text(p)`) AND the column rank (`Text(p+1) < Wext(p)`) of the
achiever chain — i.e. the residual block `r_p × c_p` (`r_p = Text(p) − Text(p+1)`, `c_p = Wext(p) −
Text(p+1)`) is nonempty. This is the decidable classifier, stated in the chain's native widths.

## The construction (cert §2, validated 285/285 + 240/240 by `witness_tide_v2_validate.py`)
Pivot at the DEEPEST such `p*`. Witness blocks: all Schur `K = I`, `X = N = 0`; the pivot
`E_{p*}(0,0) = 1`; the carriers `W_b(0, Text(b+2)) = 1` for `b ∈ [p*, L−1]`. The surviving entry of the
telescoped quotient is `Hmat 0 (ρ, 0) = 1` with `ρ = Text(p*+1)`, so `sqSumHmat0 ≥ 1² > 0`, hence
`achieverUfun w ≠ 0` (via `achieverUfun_eq_eval` + `VvalGen_eq_sqSumHmat0`).

## Reduction wiring
The block laws (`bmatStack_top`, `chainA_apply_natAdd`, `rmatPad`) feed three downward inductions:
(I-suffix) `suffix(s)(σ_s,0) = 1`; (I-base) the pivot at `p*`; (I-up) the `ρ`-row threads up through
`Bmat = [I;0]` top rows. The witness `w := wOnIdx ∘ chartIdxEquiv` reads the blocks off the role-slots
(`Equiv.apply_symm_apply` cancels the chartIdxEquiv round-trip; `frameSplitEquiv`/`liftSlotEquiv`
forward-decode the slot inside `wOnIdx`).
-/

open scoped BigOperators
open Matrix MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The abstract suffix-carrier induction

Work on the chain `c := (chainOfMt u M t B hle).toChain` (so `c.A s = Agen …`, `c.suffix` from `Chain`).
The carrier hypotheses (one per boundary `s ∈ [p, L−1]`) say the lift block `W_s = B.Wblk s` has its
`(0, σ_{s+1})` entry `= 1` and all other entries of row `0` are `0`. Then the surviving column threads:
`suffix(s)(Text(s+1), 0) = 1`, with the leaf `suffix(L)(0,0) = 1`.
-/

variable {𝕜 : Type} [CommRing 𝕜]

/-- Generic three-fold matrix reassociation (the `lean/CLAUDE.md` kernel: a fully-applied term dodges the
dependent-dimension matching that defeats `rw [Matrix.mul_assoc]`; resolves the `c.Wwid` ↔ `c.toChain.Wwid`
projection mismatch by unifying the abstract index types up to defeq). -/
theorem mul_three_reassoc' {p q r s : Type*} [Fintype p] [Fintype q] [Fintype r]
    (a : Matrix p q 𝕜) (b : Matrix q r 𝕜) (c : Matrix r s 𝕜) :
    a * b * c = a * (b * c) := Matrix.mul_assoc a b c

/-- The lift-row index `Text(s+1) + a` of the ambient width `Wext s`, as a cast `natAdd` so the
`chainA_apply_natAdd` law fires. -/
def liftRow (M t : Fin (L + 1) → ℕ) (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (s : ℕ) (hs : s < L) (a : Fin (Wext M s - Text M t (s + 1))) : Fin (Wext M s) :=
  Fin.cast (genWidthEq M t hle s hs) (Fin.natAdd (Text M t (s + 1)) a)

/-- **The achiever-chain layer `A_s` lift row reads `W_s`.** `c.A s (liftRow … a) j = (B.Wblk s) a j`
(the `chainA` lift-row law, after unfolding `c.A s = Agen … = chainA …` at `s < L`). -/
theorem chain_A_liftRow {M t : Fin (L + 1) → ℕ} {u : 𝕜} {B : GenBlk M t 𝕜}
    {hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k} (s : ℕ) (hs : s < L)
    (a : Fin (Wext M s - Text M t (s + 1))) (j : Fin (Wext M (s + 1))) :
    (chainOfMt u M t B hle).toChain.A s (liftRow M t hle s hs a) j = (B.Wblk s) a j := by
  show Agen u M t B hle s _ j = _
  unfold Agen
  rw [dif_pos hs]
  exact chainA_apply_natAdd _ _ _ _ a j

/-- A column-drop proof bundle: `Wext s − Text(s+1) ≥ 1` lets `⟨0,_⟩` index the lift block's first row. -/
def colDrop (M t : Fin (L + 1) → ℕ) (s : ℕ) : Prop := 0 < Wext M s - Text M t (s + 1)

/-- The surviving row value at chain boundary `s` (`0` at the leaf, `Text(s+1)` interior). -/
def survRowVal (M t : Fin (L + 1) → ℕ) (s : ℕ) : ℕ := if s = L then 0 else Text M t (s + 1)

/-- **The abstract suffix-carrier induction.** The surviving row of `suffix s` in column `0` has value
`survRowVal s` (`0` at the leaf, `Text(s+1)` interior), threaded by the carriers. Hypotheses:
* `hsurv` — `survRowVal s < Wext M s` on `[p, L]` (so the row index is well-typed);
* (lift) for `p ≤ s < L`, the surviving row `⟨Text(s+1),_⟩` is the FIRST lift row of `A_s`, and `B.Wblk s`
  row `0` is the `⟨survRowVal (s+1),_⟩`-indicator.

Then `suffix s ⟨survRowVal s, _⟩ 0 = 1` for `s ∈ [p, L]`. Downward induction on `d = L − s` — the row is
constructed in-place from `hsurv` (no external total `colOf`, avoiding `Wext s = 0` totality issues). -/
theorem suffix_carrier {M t : Fin (L + 1) → ℕ} {u : 𝕜} {B : GenBlk M t 𝕜}
    {hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k} {p : ℕ} (hML : 0 < Wext M L)
    -- the surviving-row of `A s` reads `B.Wblk s` row `0` — given as a single packaged hypothesis
    -- (any row index with the right `.val` works, sidestepping `Fin.mk` proof-term matching)
    (hArow : ∀ s, p ≤ s → s < L → ∀ (r : Fin (Wext M s)), r.val = survRowVal M t s →
      ∀ c : Fin (Wext M (s + 1)),
        (chainOfMt u M t B hle).toChain.A s r c
          = if c.val = survRowVal M t (s + 1) then 1 else 0)
    (hsurvW : ∀ s, p ≤ s → s ≤ L → survRowVal M t s < Wext M s)
    (d : ℕ) (s : ℕ) (hsd : s + d = L) (hps : p ≤ s)
    (r : Fin (Wext M s)) (hr : r.val = survRowVal M t s) :
    (chainOfMt u M t B hle).toChain.suffix s (by omega) r ⟨0, hML⟩ = 1 := by
  induction d generalizing s r with
  | zero =>
    obtain rfl : L = s := by omega
    -- leaf: `suffix L = 1`; the surviving row is `0` (`survRowVal L = 0`)
    have hr0 : r = ⟨0, hML⟩ := by
      apply Fin.ext; rw [hr]; simp [survRowVal]
    subst hr0
    rw [(chainOfMt u M t B hle).toChain.suffix_last]
    exact Matrix.one_apply_eq _
  | succ d ih =>
    have hs : s < L := by omega
    rw [(chainOfMt u M t B hle).toChain.suffix_succ s hs, Matrix.mul_apply]
    refine (Finset.sum_eq_single_of_mem
      (⟨survRowVal M t (s + 1), hsurvW (s + 1) (by omega) (by omega)⟩ : Fin (Wext M (s + 1)))
      (Finset.mem_univ _) ?_).trans ?_
    · intro c _ hcne
      rw [hArow s hps hs r hr c, if_neg, zero_mul]
      intro hv; exact hcne (Fin.ext (by rw [hv]))
    · rw [hArow s hps hs r hr _, if_pos rfl, one_mul]
      exact ih (s + 1) (by omega) (le_trans hps (Nat.le_succ s)) _ rfl

/-! ## The `rmatPad` entry laws (the bottom-right E-block placement)

`rmatPad … E = [[0,0],[0,E]]` reindexed: the E-block sits at residual rows/cols `Text(s+1) + ·`. The
two laws the pivot step needs: the residual×residual entry reads `E`, the residual×kept entry is `0`. -/

/-- **`rmatPad` residual×residual law**: `rmatPad … E (cast(natAdd t1 i)) (cast(natAdd t1 j)) = E i j`
(the bottom-right block; `t1 = Text(s+1)`). -/
theorem rmatPad_natAdd_natAdd {M t : Fin (L + 1) → ℕ} {s : ℕ}
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) 𝕜)
    (i : Fin (Text M t s - Text M t (s + 1))) (j : Fin (Wext M s - Text M t (s + 1))) :
    rmatPad M t s h1 h2 E
        (Fin.cast (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)
          (Fin.natAdd (Text M t (s + 1)) i))
        (Fin.cast (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)
          (Fin.natAdd (Text M t (s + 1)) j))
      = E i j := by
  simp only [rmatPad, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply,
    finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self,
    finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]

/-- **`rmatPad` residual×kept law**: the residual row, kept column entry is `0`. -/
theorem rmatPad_natAdd_castAdd {M t : Fin (L + 1) → ℕ} {s : ℕ}
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) 𝕜)
    (i : Fin (Text M t s - Text M t (s + 1))) (j : Fin (Text M t (s + 1))) :
    rmatPad M t s h1 h2 E
        (Fin.cast (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)
          (Fin.natAdd (Text M t (s + 1)) i))
        (Fin.cast (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)
          (Fin.castAdd (Wext M s - Text M t (s + 1)) j))
      = 0 := by
  simp only [rmatPad, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply,
    finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self,
    finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

/-! ## The abstract `Hmat`-row threading (I-up + I-base)

The surviving row `ρ = Text(p+1)`, typed at each level `s ≤ p` as `rhoAt s : Fin (Text s)`. For
`s < p`: `c.E s = 0` (no pivot above `p`) and `ρ < Text(s+1)` (ρ is a TOP `K = I` row of `Bmat s`), so
`Hmat s (ρ, 0) = Hmat (s+1) (ρ, 0)`. Threading from the pivot value `Hmat p (ρ, 0) = 1` down to
`Hmat 0 (ρ, 0) = 1`. -/

/-- The surviving row `Text(p+1)` typed at level `s` (`Fin (Text s)`), valid for `s ≤ p` (`Text(p+1) <
Text(p) ≤ Text(s)` along the descent). -/
def rhoAt (M t : Fin (L + 1) → ℕ) (p : ℕ) (s : ℕ) (h : Text M t (p + 1) < Text M t s) :
    Fin (Text M t s) := ⟨Text M t (p + 1), h⟩

/-- **The `Hmat`-row threading (I-up + I-base).** Given the pivot value at `p` and, for each `s < p`,
the block facts `c.E s = 0` (no pivot) + `c.B s` top-`K=I` rows + `ρ < Text(s+1)`, the surviving row
threads up: `Hmat s (rhoAt s, 0) = 1` for every `s ≤ p`. Downward induction on `d = p − s`. -/
theorem Hmat_row_thread {M t : Fin (L + 1) → ℕ} {u : 𝕜} {B : GenBlk M t 𝕜}
    {hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k} {p : ℕ} (hp : p < L) (hML : 0 < Wext M L)
    (hρT : ∀ s, s ≤ p → Text M t (p + 1) < Text M t s)
    (hdesc : ∀ s, s < p → Text M t (s + 1) ≤ Text M t s)
    (hpivot : (chainOfMt u M t B hle).toChain.Hmat p (le_of_lt hp)
        (rhoAt M t p p (hρT p (le_refl p))) ⟨0, hML⟩ = 1)
    (hEzero : ∀ s, s < p → (chainOfMt u M t B hle).toChain.E s = 0)
    (hρlt : ∀ s, s < p → Text M t (p + 1) < Text M t (s + 1))
    (hBtop : ∀ s, (hs : s < p) → ∀ (a j : Fin (Text M t (s + 1))),
      (chainOfMt u M t B hle).toChain.B s
          (Fin.cast (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by
            have := hdesc s hs; omega) (Fin.castAdd _ a)) j
        = if a = j then 1 else 0)
    (d : ℕ) (s : ℕ) (hsd : s + d = p) :
    (chainOfMt u M t B hle).toChain.Hmat s (by omega) (rhoAt M t p s (hρT s (by omega)))
        ⟨0, hML⟩ = 1 := by
  induction d generalizing s with
  | zero =>
    obtain rfl : s = p := by omega
    exact hpivot
  | succ d ih =>
    have hsp : s < p := by omega
    have hsL : s < L := by omega
    -- peel `Hmat s = B_s · Hmat (s+1) + E_s · suffix (s+1)`; the `E_s` term vanishes
    rw [(chainOfMt u M t B hle).toChain.Hmat_succ s hsL, hEzero s hsp, Matrix.zero_mul,
      add_zero, Matrix.mul_apply]
    -- `rhoAt s` is a TOP `K = I` row: `c.B s (rhoAt s) j = [rhoAt (s+1) = j]` (cast handled in-place)
    have hB : ∀ j : Fin (Text M t (s + 1)),
        (chainOfMt u M t B hle).toChain.B s (rhoAt M t p s (hρT s (by omega))) j
          = if (rhoAt M t p (s + 1) (hρlt s hsp)) = j then 1 else 0 := by
      intro j
      have hcast : (rhoAt M t p s (hρT s (by omega)))
          = Fin.cast (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by
              have := hdesc s hsp; omega)
            (Fin.castAdd _ (rhoAt M t p (s + 1) (hρlt s hsp))) := by
        apply Fin.ext; simp [rhoAt]
      rw [hcast]; exact hBtop s hsp (rhoAt M t p (s + 1) (hρlt s hsp)) j
    refine (Finset.sum_eq_single_of_mem (rhoAt M t p (s + 1) (hρlt s hsp))
      (Finset.mem_univ _) ?_).trans ?_
    · intro j _ hjne
      rw [hB j, if_neg (fun h => hjne h.symm), zero_mul]
    · rw [hB (rhoAt M t p (s + 1) (hρlt s hsp)), if_pos rfl, one_mul]
      exact ih (s + 1) (by omega)

/-! ## The pivot step (I-base): `Hmat p (rhoAt p, 0) = 1`

At the deepest pivot `p`, the row `ρ = Text(p+1)` is the first BOTTOM row of `B_p = [K ; X·K]` (so the
`B_p·Hmat(p+1)` term vanishes since `X·K = 0`), and the `E_p · suffix(p+1)` term reassociates to
`Rmat_p · suffix p` (`E_p = Rmat_p · A_p`, `A_p · suffix(p+1) = suffix p`); the `rmatPad` pivot picks out
the surviving column, giving `suffix p (colOf p, 0) = 1`. -/

/-- **The pivot value `Hmat p (ρ, 0) = 1`.** Hypotheses: the `B_p` row-`ρ` vanishes (`hBbot`, the
`X·K = 0` bottom row); `E_p = Rmat_p · A_p` (definitional); the `Rmat_p` row-`ρ` indicator on `colP`
(`hRmat`); the surviving suffix entry (`hsuffix`). -/
theorem Hmat_pivot {M t : Fin (L + 1) → ℕ} {u : 𝕜} {B : GenBlk M t 𝕜}
    {hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k} {p : ℕ} (hp : p < L) (hML : 0 < Wext M L)
    (colP : Fin (Wext M p)) (ρcast : Fin (Text M t p))
    (hBbot : ∀ j : Fin (Text M t (p + 1)),
      (chainOfMt u M t B hle).toChain.B p ρcast j = 0)
    (hRmat : ∀ c : Fin (Wext M p), B.Rmat p ρcast c = if c = colP then 1 else 0)
    (hsuffix : (chainOfMt u M t B hle).toChain.suffix p (le_of_lt hp) colP ⟨0, hML⟩ = 1) :
    (chainOfMt u M t B hle).toChain.Hmat p (le_of_lt hp) ρcast ⟨0, hML⟩ = 1 := by
  -- peel `Hmat p = B_p · Hmat (p+1) + E_p · suffix (p+1)`
  rw [(chainOfMt u M t B hle).toChain.Hmat_succ p hp, Matrix.add_apply]
  -- term 1: `(B_p · Hmat (p+1)) (ρ, 0) = 0` (the whole `ρ`-row of `B_p` is `0`)
  have hterm1 : ((chainOfMt u M t B hle).toChain.B p
      * (chainOfMt u M t B hle).toChain.Hmat (p + 1) (by omega)) ρcast ⟨0, hML⟩ = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero (fun j _ => by rw [hBbot j, zero_mul])
  rw [hterm1, zero_add]
  -- term 2: `E_p = Rmat_p · A_p`; reassociate `(Rmat·A)·suffix(p+1) = Rmat·(A·suffix(p+1)) =
  -- Rmat·suffix p` (matrices ascribed to literal `Wext`/`Text` types so the `c.Wwid`/`c.toChain.Wwid`
  -- projection mismatch never reaches `HMul` synthesis), then collapse the sum.
  set c := chainOfMt u M t B hle with hc
  let Rp : Matrix (Fin (Text M t p)) (Fin (Wext M p)) 𝕜 := c.Rmat p
  let Ap : Matrix (Fin (Wext M p)) (Fin (Wext M (p + 1))) 𝕜 := c.A p
  let Sp : Matrix (Fin (Wext M (p + 1))) (Fin (Wext M L)) 𝕜 :=
    c.toChain.suffix (p + 1) (by omega)
  let Ep : Matrix (Fin (Text M t p)) (Fin (Wext M (p + 1))) 𝕜 := c.toChain.E p
  let Spp : Matrix (Fin (Wext M p)) (Fin (Wext M L)) 𝕜 := c.toChain.suffix p (le_of_lt hp)
  have hsucc : (Spp : Matrix (Fin (Wext M p)) (Fin (Wext M L)) 𝕜) = Ap * Sp :=
    c.toChain.suffix_succ p hp
  have hreassoc : Ep * Sp = Rp * Spp := by
    rw [hsucc, show Ep = Rp * Ap from rfl]
    exact mul_three_reassoc' Rp Ap Sp
  show (Ep * Sp) ρcast ⟨0, hML⟩ = 1
  rw [hreassoc, Matrix.mul_apply]
  refine (Finset.sum_eq_single_of_mem colP (Finset.mem_univ _) ?_).trans ?_
  · intro cc _ hcne
    rw [show Rp ρcast cc = B.Rmat p ρcast cc from rfl, hRmat cc, if_neg hcne, zero_mul]
  · rw [show Rp ρcast colP = B.Rmat p ρcast colP from rfl, hRmat colP, if_pos rfl, one_mul]
    show (chainOfMt u M t B hle).toChain.suffix p (le_of_lt hp) colP ⟨0, hML⟩ = 1
    exact hsuffix

/-- **The INTERIOR-drop classifier (chain-native widths).** Some interior chain boundary
`p ∈ [1, L−1]` drops the row rank (`Text(p+1) < Text(p)`), and the column rank drops at every boundary
of the tail `[p, L−1]` (`Text(b+1) < Wext(b)`) — so a `u`-pivot at `p` and surviving-column carriers on
the whole tail are placeable. This is exactly the cert's interior class: validated `H ↔ interior`,
285/285 over the `1..3`/`L∈{2,3,4}` grid (the deepest interior `p*` always yields tail column-drop). -/
def InteriorDrop (M : Fin (L + 1) → ℕ) : Prop :=
  0 < Wext M L ∧ ∃ p, 1 ≤ p ∧ p < L ∧ Text M (tach M) (p + 1) < Text M (tach M) p ∧
    ∀ b, p ≤ b → b < L → Text M (tach M) (b + 1) < Wext M b

/-! ## The witness coordinate vector

`w := wOnIdx ∘ chartIdxEquiv`, reading role-slots through `frameSplitEquiv`/`liftSlotEquiv` (forward) so
the structured decoder's readers take the cert's witness-block values. The surviving column at chain
boundary `s` is `survCol s := (if s = L then 0 else Text(s+1))` (the `colOf` value); the carrier at
boundary `b` lives at lift-row `0`, lift-column `survCol (b+1)`. -/

/-- The surviving-column value at chain boundary `s`: `0` at the leaf `L`, else `Text(s+1)`. -/
noncomputable def survCol (M : Fin (L + 1) → ℕ) (s : ℕ) : ℕ :=
  if s = L then 0 else Text M (tach M) (s + 1)

/-- **The witness reader-value function on `ChartIdx`.** Decodes the role-slot (`frameSplitEquiv` for the
Schur block, `liftSlotEquiv` for the lift) and returns the cert's witness-block value: `K` is the
identity (diagonal), `X = N = 0`, `E` is the pivot `(0,0) = 1` at boundary `p`, the lift `W` is the
surviving-column carrier `(0, survCol(k+2)) = 1`. The pivot tag `p` and `ha` are parameters. -/
noncomputable def wOnIdx (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (p : ℕ) :
    ChartIdx M (tDesc M (tach M)) → ℝ := fun q =>
  match q with
  | ⟨k, Sum.inl s⟩ =>
    match frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>  -- K role
      let ij := finProdFinEquiv.symm qK
      if ij.1 = ij.2 then 1 else 0
    | Sum.inr qE =>  -- E role
      let ij := finProdFinEquiv.symm qE
      if k.val + 1 = p ∧ ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0
    | _ => 0  -- X, N roles
  | ⟨k, Sum.inr l⟩ =>
    if hk : k.val + 1 < L then
      let ij := liftSlotEquiv M (tDesc M (tach M)) k.val hk l
      if ij.1.val = 0 ∧ ij.2.val = survCol M (k.val + 2) then 1 else 0
    else 0

/-- **The witness coordinate vector** `wInt := wOnIdx ∘ chartIdxEquiv` (`Fin (routeMAmbient M) → ℝ`). -/
noncomputable def wInt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (p : ℕ) :
    Fin (routeMAmbient M) → ℝ :=
  wOnIdx M ha p ∘ chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL

/-! ## The reader-value lemmas (the witness realizes the cert's blocks)

Each reader composes `chartIdxEquiv.symm` with a role-slot injection; `wInt = wOnIdx ∘ chartIdxEquiv`
cancels the `chartIdxEquiv` round-trip (`apply_symm_apply`), then `wOnIdx` forward-decodes the same
role-slot (`frameSplitEquiv`/`liftSlotEquiv` `apply_symm_apply`) and `finProdFinEquiv` round-trips. -/

/-- **`readK` reads the identity.** `readK (wInt) ⟨k,hk⟩ i j = if i = j then 1 else 0`. -/
theorem readK_wInt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (p : ℕ) (k : Fin L)
    (i j : Fin (Text M (tach M) (k.val + 2))) :
    readK M (tach M) ha (wInt M ha p) k i j = if i = j then 1 else 0 := by
  rw [readK, wInt, Function.comp_apply, Equiv.apply_symm_apply, wOnIdx,
    Equiv.apply_symm_apply]
  simp only [Equiv.symm_apply_apply]

/-- **`readX` reads zero.** -/
theorem readX_wInt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (p : ℕ) (k : Fin L)
    (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Text M (tach M) (k.val + 2))) :
    readX M (tach M) ha (wInt M ha p) k i j = 0 := by
  rw [readX, wInt, Function.comp_apply, Equiv.apply_symm_apply, wOnIdx, Equiv.apply_symm_apply]

/-- **`readN` reads zero.** -/
theorem readN_wInt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (p : ℕ) (k : Fin L)
    (i : Fin (Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) :
    readN M (tach M) ha (wInt M ha p) k i j = 0 := by
  rw [readN, wInt, Function.comp_apply, Equiv.apply_symm_apply, wOnIdx, Equiv.apply_symm_apply]

/-- **`readE` reads the pivot indicator.** `readE (wInt) ⟨k,hk⟩ i j = 1` iff `k+1 = p` and `(i,j) =
(0,0)`. -/
theorem readE_wInt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (p : ℕ) (k : Fin L)
    (i : Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) :
    readE M (tach M) ha (wInt M ha p) k i j
      = if k.val + 1 = p ∧ i.val = 0 ∧ j.val = 0 then 1 else 0 := by
  rw [readE, wInt, Function.comp_apply, Equiv.apply_symm_apply, wOnIdx, Equiv.apply_symm_apply]
  simp only [Equiv.symm_apply_apply]

/-- **`readW` reads the surviving-column carrier.** `readW (wInt) ⟨k,hk⟩ i j = 1` iff `i = 0` and
`j = survCol(k+2)`. -/
theorem readW_wInt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (p : ℕ) (k : Fin L)
    (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) (j : Fin (Wext M (k.val + 2))) :
    readW M (tach M) ha (wInt M ha p) k hk i j
      = if i.val = 0 ∧ j.val = survCol M (k.val + 2) then 1 else 0 := by
  rw [readW, wInt, Function.comp_apply, Equiv.apply_symm_apply, wOnIdx]
  rw [dif_pos hk]
  simp only [Equiv.apply_symm_apply]

/-! ## The block-shape discharges (the decoder's `Bmat`/`Rmat`/`Wblk` at the witness)

`genBlkFlatStruct … (wInt) .Bmat (k+1) = bmatStack (readK = I) (readX = 0)`, etc. The `bmatStack`/`rmatPad`
entry laws + the reader values give the abstract-induction hypotheses. The interior boundaries are
`k+1 ≥ 1`; the identity boundary `0` is handled separately in the threading base. -/

/-- `rmatPad` of the zero `E`-block is the zero matrix. -/
theorem rmatPad_zero {M' t' : Fin (L + 1) → ℕ} {s : ℕ} (h1 : Text M' t' (s + 1) ≤ Text M' t' s)
    (h2 : Text M' t' (s + 1) ≤ Wext M' s) :
    rmatPad M' t' s h1 h2 (0 : Matrix (Fin (Text M' t' s - Text M' t' (s + 1)))
      (Fin (Wext M' s - Text M' t' (s + 1))) ℝ) = 0 := by
  unfold rmatPad
  rw [Matrix.fromBlocks_zero]
  simp [Matrix.reindex_apply]

variable {M : Fin (L + 1) → ℕ} (ha : StructAdm M (tach M)) (p : ℕ)

/-- The witness `Bmat (k+1)` top rows are the identity (`K = readK = I`). -/
theorem genBlk_Bmat_succ_top (k : ℕ) (hk : k < L)
    (a j : Fin (Text M (tach M) (k + 2))) :
    (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Bmat (k + 1)
        (Fin.cast (show Text M (tach M) (k + 2)
              + (Text M (tach M) (k + 1) - Text M (tach M) (k + 2)) = Text M (tach M) (k + 1) by
            have := ha.hdesc k hk; omega) (Fin.castAdd _ a)) j
      = if a = j then 1 else 0 := by
  show (if hk' : k < L then bmatStack M (tach M) (k + 1) (ha.hdesc k hk')
          (readK M (tach M) ha (wInt M ha p) ⟨k, hk'⟩)
          (readX M (tach M) ha (wInt M ha p) ⟨k, hk'⟩) else 0) _ j = _
  rw [dif_pos hk, bmatStack_top, readK_wInt]

/-- The witness identity-boundary `Bmat 0 = reindex 1` top rows are the identity. (`Text 0 = Text 1`, so
the residual block is empty and `castAdd a` is `a`.) The `s = 0` case of the `Hmat`-threading `hBtop`. -/
theorem genBlk_Bmat_zero_top (a j : Fin (Text M (tach M) 1))
    (hcast : Text M (tach M) 1 + (Text M (tach M) 0 - Text M (tach M) 1) = Text M (tach M) 0) :
    (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Bmat 0
        (Fin.cast hcast (Fin.castAdd _ a)) j
      = if a = j then 1 else 0 := by
  show (Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M (tach M) ha.h0))
      (1 : Matrix (Fin (Text M (tach M) 0)) (Fin (Text M (tach M) 0)) ℝ)) _ j = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : a = j
  · rw [if_pos h, if_pos]
    apply Fin.ext
    simp only [Equiv.refl_symm, Equiv.refl_apply, finCongr_symm, finCongr_apply,
      Fin.val_cast, Fin.val_castAdd, h]
  · rw [if_neg h, if_neg]
    intro hcontra
    apply h
    apply Fin.ext
    have hvv := congrArg Fin.val hcontra
    simp only [Equiv.refl_symm, Equiv.refl_apply, finCongr_symm, finCongr_apply,
      Fin.val_cast, Fin.val_castAdd] at hvv
    exact hvv

/-- The witness `Bmat (k+1)` bottom rows vanish (`X·K = 0·K = 0`). -/
theorem genBlk_Bmat_succ_bot (k : ℕ) (hk : k < L)
    (b : Fin (Text M (tach M) (k + 1) - Text M (tach M) (k + 2)))
    (j : Fin (Text M (tach M) (k + 2))) :
    (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Bmat (k + 1)
        (Fin.cast (show Text M (tach M) (k + 2)
              + (Text M (tach M) (k + 1) - Text M (tach M) (k + 2)) = Text M (tach M) (k + 1) by
            have := ha.hdesc k hk; omega) (Fin.natAdd _ b)) j
      = 0 := by
  show (if hk' : k < L then bmatStack M (tach M) (k + 1) (ha.hdesc k hk')
          (readK M (tach M) ha (wInt M ha p) ⟨k, hk'⟩)
          (readX M (tach M) ha (wInt M ha p) ⟨k, hk'⟩) else 0) _ j = _
  rw [dif_pos hk, bmatStack_bot]
  -- `(readX · readK) b j = 0` since `readX = 0`
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero (fun c _ => by rw [readX_wInt, zero_mul])

/-- The witness `Rmat (k+1) = 0` away from the pivot (`k+1 ≠ p`): `readE = 0`, so `rmatPad 0 = 0`. -/
theorem genBlk_Rmat_succ_zero (k : ℕ) (hk : k < L) (hkp : k + 1 ≠ p) :
    (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Rmat (k + 1) = 0 := by
  show (if hk' : k < L then rmatPad M (tach M) (k + 1) (ha.hdesc k hk') (ha.hub k)
          (readE M (tach M) ha (wInt M ha p) ⟨k, hk'⟩) else 0) = 0
  rw [dif_pos hk]
  have hEz : readE M (tach M) ha (wInt M ha p) ⟨k, hk⟩ = 0 := by
    funext i j
    rw [readE_wInt, if_neg (fun h => hkp h.1)]; rfl
  rw [hEz]
  exact rmatPad_zero _ _

/-- The witness `c.E s = 0` away from the pivot (`s ≠ p`): `B.Rmat s = 0` ⟹ `E_s = Rmat_s · A_s = 0`. -/
theorem genBlk_E_zero (u : ℝ) (hle : ∀ k, k < L → Text M (tach M) (k + 1) ≤ Wext M k)
    (s : ℕ) (hs : s < L) (hsp : s ≠ p) :
    (chainOfMt u M (tach M) (genBlkFlatStruct M (tach M) ha (wInt M ha p)) hle).toChain.E s = 0 := by
  -- `E_s = Rmat_s · A_s` and `Rmat_s = 0`
  show (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Rmat s
      * Agen u M (tach M) (genBlkFlatStruct M (tach M) ha (wInt M ha p)) hle s = 0
  have hRz : (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Rmat s = 0 := by
    match s with
    | 0 => rfl
    | (k + 1) => exact genBlk_Rmat_succ_zero ha p k (by omega) (by omega)
  rw [hRz, Matrix.zero_mul]

/-- **The witness pivot `Rmat p` indicator.** At the pivot boundary `p = k+1`, with the row the first
residual row (`natAdd 0`) and the column the first residual column (`natAdd 0` as `colP`), `Rmat p` is the
`colP`-indicator (the `rmatPad` of the pivot `E(0,0) = 1`). -/
theorem genBlk_Rmat_pivot (k : ℕ) (hk : k < L)
    (hr : Text M (tach M) (k + 2) < Text M (tach M) (k + 1))
    (hcd : Text M (tach M) (k + 2) < Wext M (k + 1))
    (c : Fin (Wext M (k + 1))) :
    (genBlkFlatStruct M (tach M) ha (wInt M ha (k + 1))).Rmat (k + 1)
        (Fin.cast (show Text M (tach M) (k + 2)
              + (Text M (tach M) (k + 1) - Text M (tach M) (k + 2)) = Text M (tach M) (k + 1) by omega)
          (Fin.natAdd _ ⟨0, by omega⟩)) c
      = if c = Fin.cast (show Text M (tach M) (k + 2)
              + (Wext M (k + 1) - Text M (tach M) (k + 2)) = Wext M (k + 1) by omega)
          (Fin.natAdd _ ⟨0, by omega⟩) then 1 else 0 := by
  show (if hk' : k < L then rmatPad M (tach M) (k + 1) (ha.hdesc k hk') (ha.hub k)
          (readE M (tach M) ha (wInt M ha (k + 1)) ⟨k, hk'⟩) else 0) _ c = _
  rw [dif_pos hk]
  -- write `c` as a cast of a `castAdd`/`natAdd` (kept / residual columns) and split
  have hcd' : Text M (tach M) (k + 1 + 1) ≤ Wext M (k + 1) := le_of_lt hcd
  set hWeq : Text M (tach M) (k + 1 + 1) + (Wext M (k + 1) - Text M (tach M) (k + 1 + 1))
      = Wext M (k + 1) := by omega with hWeqdef
  obtain ⟨cs, hcs⟩ : ∃ cs, c = Fin.cast hWeq (finSumFinEquiv cs) :=
    ⟨finSumFinEquiv.symm (Fin.cast hWeq.symm c), by
      rw [Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_eq_self]⟩
  subst hcs
  rcases cs with j' | j'
  · -- kept column `castAdd j'`: `rmatPad` residual×kept = 0; and `castAdd ≠ natAdd 0`
    rw [finSumFinEquiv_apply_left, rmatPad_natAdd_castAdd, if_neg]
    intro hcontra
    have hv := congrArg Fin.val hcontra
    have hjlt : j'.val < Text M (tach M) (k + 2) := j'.isLt
    simp only [Fin.val_cast, finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.val_natAdd,
      Fin.val_zero, show k + 1 + 1 = k + 2 from rfl, add_zero] at hv
    exact absurd (hv ▸ hjlt) (lt_irrefl _)
  · -- residual column `natAdd j'`: `rmatPad` residual×residual = `readE 0 j'` = `[j'.val = 0]`
    rw [finSumFinEquiv_apply_right, rmatPad_natAdd_natAdd, readE_wInt]
    by_cases hj0 : j'.val = 0
    · rw [if_pos ⟨rfl, rfl, hj0⟩, if_pos]
      apply Fin.ext
      simp only [Fin.val_cast, finSumFinEquiv_apply_right, Fin.val_natAdd, Fin.val_zero, hj0]
    · rw [if_neg (fun h => hj0 h.2.2), if_neg]
      intro hcontra
      have hv := congrArg Fin.val hcontra
      simp only [Fin.val_cast, finSumFinEquiv_apply_right, Fin.val_natAdd, Fin.val_zero,
        show k + 1 + 1 = k + 2 from rfl] at hv
      omega

/-- **`sqSumHmat0 ≠ 0` from a surviving unit entry.** If `Hmat 0 (ρ, c₀) = 1`, the sum of squares is
`≥ 1 > 0`. -/
theorem sqSumHmat0_ne_zero_of_entry {n : ℕ} {u₀ : ℝ} (c : Chain n u₀)
    (ρ : Fin (c.Twid 0)) (c₀ : Fin (c.Wwid n)) (hentry : c.Hmat 0 (Nat.zero_le n) ρ c₀ = 1) :
    sqSumHmat0 c ≠ 0 := by
  intro h0
  -- each summand is `≥ 0`; the total is `0` ⟹ every summand `0`; but `(Hmat 0 ρ c₀)² = 1 ≠ 0`
  have hterm : (c.Hmat 0 (Nat.zero_le n) ρ c₀) ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < sqSumHmat0 c := by
      unfold sqSumHmat0
      apply Finset.sum_pos'
      · exact fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)
      · exact ⟨ρ, Finset.mem_univ _, Finset.sum_pos'
          (fun j _ => sq_nonneg _) ⟨c₀, Finset.mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)⟩⟩
    exact (ne_of_gt hpos) h0
  rw [hentry, one_pow] at hterm
  exact one_ne_zero hterm

/-- **The interior-drop pivot-survival witness** (the sole remaining `Ubound` input on this class):
there is a flat point where the achiever unit is nonzero. The witness `wInt` realizes the cert's blocks;
the three abstract inductions give the surviving entry `Hmat 0 (Text(p+1), 0) = 1 ≠ 0`. -/
theorem exists_achieverUfun_ne_zero_interior (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hN : 0 < routeMAmbient M) (hInt : InteriorDrop M) :
    ∃ w : Fin (routeMAmbient M) → ℝ, achieverUfun M hL hN w ≠ 0 := by
  obtain ⟨hML, p, hp1, hpL, hr, hcd⟩ := hInt
  set ha := structAdm_tach M hL with hadef
  set hle := hleStruct M (tach M) ha with hledef
  -- the witness vector
  refine ⟨wInt M ha p, ?_⟩
  -- reduce `achieverUfun w` to `sqSumHmat0` of the ℝ decoder chain
  rw [achieverUfun_eq_eval hL hN, eval_UPolyGen]
  -- the chain at the witness
  set u := wInt M ha p (structPivot M hN) with hudef
  set B := genBlkFlatStruct M (tach M) ha (wInt M ha p) with hBdef
  set c := (chainOfMt u M (tach M) B hle).toChain with hcdef
  -- the surviving row value at the pivot, and the descent facts
  have hTdesc : ∀ s, s < p → Text M (tach M) (s + 1) ≤ Text M (tach M) s := by
    intro s hsp
    match s with
    | 0 => exact le_of_eq (Text0_eq_Text1_struct M (tach M) ha.h0).symm
    | (k + 1) => exact ha.hdesc k (by omega)
  -- `Text` is weakly decreasing on the interior: `Text (a + d) ≤ Text a` when `a + d ≤ p`
  have hTle : ∀ d a, a + d ≤ p → Text M (tach M) (a + d) ≤ Text M (tach M) a := by
    intro d
    induction d with
    | zero => intro a _; rw [Nat.add_zero]
    | succ e ih =>
      intro a ha'
      calc Text M (tach M) (a + (e + 1)) = Text M (tach M) ((a + e) + 1) := by ring_nf
        _ ≤ Text M (tach M) (a + e) := hTdesc (a + e) (by omega)
        _ ≤ Text M (tach M) a := ih a (by omega)
  -- `ρ = Text(p+1) < Text(s+1)` for `s < p`: `Text(p+1) < Text(p) ≤ Text(s+1)`
  have hρlt : ∀ s, s < p → Text M (tach M) (p + 1) < Text M (tach M) (s + 1) := by
    intro s hsp
    have : Text M (tach M) ((s + 1) + (p - (s + 1))) ≤ Text M (tach M) (s + 1) :=
      hTle (p - (s + 1)) (s + 1) (by omega)
    rw [show (s + 1) + (p - (s + 1)) = p by omega] at this
    exact lt_of_lt_of_le hr this
  -- the surviving-row val `< Wext` on `[p, L]` (leaf via `hML`; interior via col-drop `hcd`)
  have hsurvW : ∀ s, p ≤ s → s ≤ L → survRowVal M (tach M) s < Wext M s := by
    intro s hps hsL
    by_cases hsl : s = L
    · subst hsl; simpa [survRowVal] using hML
    · simp only [survRowVal, if_neg hsl]; exact hcd s hps (by omega)
  -- (I-suffix) `suffix s (survRowVal s) 0 = 1` for `s ∈ [p, L]`, via the carrier reader
  have hsuffix : ∀ s, p ≤ s → ∀ (r : Fin (Wext M s)), r.val = survRowVal M (tach M) s →
      ∀ (hsL : s ≤ L), c.suffix s hsL r ⟨0, hML⟩ = 1 := by
    intro s hps r hr hsL
    refine suffix_carrier hML (fun s' hps' hs' r' hr' c' => ?_) hsurvW (L - s) s (by omega) hps r hr
    -- `A s' r' c' = [c'.val = survRowVal (s'+1)]`: `r'` is the first lift row (val = Text(s'+1))
    have hcds' : 0 < Wext M s' - Text M (tach M) (s' + 1) := by
      have := hcd s' hps' (by omega)
      simp only [survRowVal, if_neg (by omega : s' ≠ L)] at hr'; omega
    have hrlift : r' = liftRow M (tach M) hle s' hs' ⟨0, hcds'⟩ := by
      apply Fin.ext
      simp only [liftRow, Fin.val_cast, Fin.val_natAdd, hr']
      simp only [survRowVal, if_neg (by omega : s' ≠ L), Nat.add_zero]
    rw [hrlift, chain_A_liftRow s' hs' _ c']
    -- `Wblk s' 0 c' = readW (s'-1) … = carrier indicator`
    obtain ⟨k, rfl⟩ : ∃ k, s' = k + 1 := ⟨s' - 1, by omega⟩
    show (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Wblk (k + 1) _ c' = _
    rw [show (genBlkFlatStruct M (tach M) ha (wInt M ha p)).Wblk (k + 1)
          = (if hk : k < L then (if hk2 : k + 1 < L then
              readW M (tach M) ha (wInt M ha p) ⟨k, hk⟩ hk2 else 0) else 0) from rfl,
      dif_pos (by omega), dif_pos hs', readW_wInt]
    simp only [survCol, survRowVal, Fin.val_zero, true_and]
    rfl
  -- the pivot boundary `p = kp + 1`
  obtain ⟨kp, rfl⟩ : ∃ kp, p = kp + 1 := ⟨p - 1, by omega⟩
  have hkpL : kp < L := by omega
  have hr2 : Text M (tach M) (kp + 2) < Text M (tach M) (kp + 1) := hr
  have hcd2 : Text M (tach M) (kp + 2) < Wext M (kp + 1) := hcd (kp + 1) (le_refl _) hpL
  -- the pivot row `ρ = Text(kp+2)` (first residual row) and column `colP` (first residual col)
  set ρcast : Fin (Text M (tach M) (kp + 1)) :=
    Fin.cast (show Text M (tach M) (kp + 2) + (Text M (tach M) (kp + 1) - Text M (tach M) (kp + 2))
        = Text M (tach M) (kp + 1) by omega) (Fin.natAdd _ ⟨0, by omega⟩) with hρcastdef
  set colP : Fin (Wext M (kp + 1)) :=
    Fin.cast (show Text M (tach M) (kp + 2) + (Wext M (kp + 1) - Text M (tach M) (kp + 2))
        = Wext M (kp + 1) by omega) (Fin.natAdd _ ⟨0, by omega⟩) with hcolPdef
  have hρval : ρcast.val = Text M (tach M) (kp + 1 + 1) := by
    simp only [hρcastdef, Fin.val_cast, Fin.val_natAdd, Fin.val_zero, Nat.add_zero]
  have hcolPval : colP.val = survRowVal M (tach M) (kp + 1) := by
    simp only [hcolPdef, Fin.val_cast, Fin.val_natAdd, Fin.val_zero, Nat.add_zero, survRowVal,
      if_neg (by omega : kp + 1 ≠ L)]
  -- (I-base) `Hmat (kp+1) (ρ, 0) = 1`
  have hpivot : c.Hmat (kp + 1) (le_of_lt hpL) ρcast ⟨0, hML⟩ = 1 := by
    refine Hmat_pivot hpL hML colP ρcast ?_ ?_ ?_
    · -- `B.Bmat (kp+1)` row `ρ` (first bottom row) is `0`
      intro j
      exact genBlk_Bmat_succ_bot ha (kp + 1) kp hkpL ⟨0, by omega⟩ j
    · -- `B.Rmat (kp+1)` row `ρ` is the `colP`-indicator
      intro cc
      exact genBlk_Rmat_pivot ha kp hkpL hr2 hcd2 cc
    · -- the surviving suffix entry, from `hsuffix`
      exact hsuffix (kp + 1) (le_refl _) colP hcolPval (le_of_lt hpL)
  -- `hρT` for the threading: `Text(kp+2) < Text s` for `s ≤ kp+1` (`Text(kp+2) < Text(kp+1) ≤ Text s`)
  have hρT : ∀ s, s ≤ kp + 1 → Text M (tach M) (kp + 1 + 1) < Text M (tach M) s := by
    intro s hs
    have hle' : Text M (tach M) (kp + 1) ≤ Text M (tach M) s := by
      have := hTle (kp + 1 - s) s (by omega)
      rwa [show s + (kp + 1 - s) = kp + 1 by omega] at this
    exact lt_of_lt_of_le hr2 hle'
  -- (I-up + I-base) `Hmat 0 (ρ, 0) = 1` (thread the row up to `0`)
  have hHmat0 : c.Hmat 0 (Nat.zero_le L) (rhoAt M (tach M) (kp + 1) 0 (hρT 0 (by omega)))
      ⟨0, hML⟩ = 1 := by
    refine Hmat_row_thread (B := B) hpL hML hρT (fun s hs => hTdesc s (by omega))
      ?_ (fun s hs => genBlk_E_zero ha (kp + 1) u hle s (by omega) (by omega))
      (fun s hs => hρlt s (by omega)) ?_ (kp + 1) 0 (by omega)
    · -- `hpivot` aligned to `Hmat_row_thread`'s `rhoAt` form
      convert hpivot using 2
    · -- `hBtop` for `s < kp+1`: identity boundary `0` (`reindex 1`) + interior `k+1` (`bmatStack`)
      intro s hsp a j
      match s with
      | 0 => exact genBlk_Bmat_zero_top ha (kp + 1) a j _
      | (kk + 1) => exact genBlk_Bmat_succ_top ha (kp + 1) kk (by omega) a j
  -- `sqSumHmat0 ≠ 0` from the surviving entry
  exact sqSumHmat0_ne_zero_of_entry c (rhoAt M (tach M) (kp + 1) 0 (hρT 0 (by omega))) ⟨0, hML⟩ hHmat0

/-- **`Ubound` closes for interior-drop `M`**: the full a.e.-positivity field on the source box, with
ONLY the interior-drop hypothesis (no separate witness assumption). -/
theorem achieverUbound_interior (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
    (hInt : InteriorDrop M) :
    ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
      (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ),
        achieverUfun M hL hN u ≤ B) ∧
      ∀ᵐ u ∂(volume.restrict
          (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))),
        0 < achieverUfun M hL hN u := by
  obtain ⟨w, hw⟩ := exists_achieverUfun_ne_zero_interior M hL hN hInt
  exact achieverUbound hL hN w hw

end DLNFibre.DLN.RLCT
