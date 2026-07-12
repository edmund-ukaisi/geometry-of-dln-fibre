import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import Mathlib.GroupTheory.Perm.Sign

/-!
# `DLNFibre.DLN.RLCT.Validate.MinAdmPermInvariance` — permutation-invariance of `minAdm`

The QIP quantity `minAdm M` (the minimal admissible codim of the DLN chain `M`, `RouteMLayerSplit`)
is invariant under permuting the entries of `M`:

    `minAdm (M ∘ σ) = minAdm M`   for every `σ : Equiv.Perm (Fin (L + 1))`.

This is the `(□)`-soundness fact (the general-width no-collapse closure) and the combinatorial half of
the paper's permutation-invariance headline for `(C, θ)`.

**Proof (cover's certificate, `threads/genm-sj5/minadm-perminv-cert.md`).** `minAdm` is not manifestly
symmetric — its recursion `minAdmRec` peels the FRONT PAIR `(M₀, M₁)`. Invariance is proved by reducing
to ADJACENT transpositions (which generate `Sₙ`, `Equiv.Perm.mclosure_swap_castSucc_succ`):

* **τ₀** (swap positions `0,1`): manifest — the peel term `(M₀−t)(M₁−t)` and the bound `min(M₀,M₁)` are
  symmetric in `M₀, M₁`.
* **τ₁** (swap positions `1,2`): the CRUX. Unrolling two peels, both sides equal
  `⨅ v [ g (M₀−v) (M₁−v) (M₂−v) + minAdmRec (v, M₃, …) ]` with `g` the two-parameter minimum
  `g a b c = ⨅_{s ≤ min a b} [(a−s)(b−s) + s·c]`; the crux `gCrux_symm : g a b c = g a c b` closes it.
* **τ_{k+2}** (swap positions `k+2, k+3`): peel the (untouched) front pair, reducing to τ_{k+1} on the
  one-shorter reduced chain `redChain t M`; the arity induction (`minAdmRec_eq_minAdm` transfers to
  `minAdmRec`) supplies invariance there.

The crux `gCrux_symm` is an elementary integer fact: with `s* = a − s'` a genuine reflection when
`a − s' ≤ b`, the two parabolas-in-`s` agree pointwise (`ring` over ℤ); the boundary case uses
`(a − s' − b)(c − s') ≥ 0`.
-/

open scoped BigOperators
open Finset

namespace DLNFibre.DLN.RLCT

/-! ## The crux — the two-parameter minimum `g a b c` is symmetric in `b, c` -/

/-- **The crux minimum `g a b c = ⨅_{s ≤ min a b} [(a − s)(b − s) + s·c]`.** The value emitted by
unrolling two front-peels of `minAdmRec` on a `(a, b, c, tail)` chain (after shifting by the deep pivot). -/
def gCrux (a b c : ℕ) : ℕ :=
  (Finset.range (min a b + 1)).inf' (by simp) (fun s => (a - s) * (b - s) + s * c)

/-- The `s`-cell value of `gCrux`. -/
theorem gCrux_le_cell (a b c : ℕ) {s : ℕ} (hs : s ≤ min a b) :
    gCrux a b c ≤ (a - s) * (b - s) + s * c :=
  Finset.inf'_le _ (by rw [Finset.mem_range]; omega)

/-- **The crux `≤` (one direction, all `a b c`).** `gCrux a b c ≤ gCrux a c b`. Take the achiever `s'`
of the RHS (`s' ≤ min a c`); the reflected point `s = a − s'` witnesses the LHS when `a − s' ≤ b`
(pointwise-equal parabola values, `ring` over ℤ), else the boundary `s = b` does (via
`(a − s' − b)(c − s') ≥ 0`). -/
theorem gCrux_le (a b c : ℕ) : gCrux a b c ≤ gCrux a c b := by
  obtain ⟨s', hs'mem, hs'eq⟩ :=
    Finset.exists_mem_eq_inf' (s := Finset.range (min a c + 1)) (by simp)
      (fun s => (a - s) * (c - s) + s * b)
  rw [Finset.mem_range] at hs'mem
  have hs'ac : s' ≤ min a c := by omega
  have hs'a : s' ≤ a := le_trans hs'ac (min_le_left _ _)
  have hs'c : s' ≤ c := le_trans hs'ac (min_le_right _ _)
  have hgcb : gCrux a c b = (a - s') * (c - s') + s' * b := hs'eq
  rw [hgcb]
  by_cases hcase : a - s' ≤ b
  · -- reflection witness s = a - s' ∈ [0, min a b]; parabola values agree (ring over ℤ).
    have hsle : a - s' ≤ min a b := by omega
    refine le_trans (gCrux_le_cell a b c hsle) (le_of_eq ?_)
    -- (a - (a - s'))(b - (a - s')) + (a - s')·c = (a - s')(c - s') + s'·b
    rw [← Nat.cast_inj (R := ℤ)]
    push_cast [Nat.cast_sub (show a - s' ≤ a by omega), Nat.cast_sub hcase, Nat.cast_sub hs'a,
      Nat.cast_sub hs'c]
    ring
  · -- boundary witness s = b (needs b ≤ a, from ¬(a - s' ≤ b) ⟹ a > b).
    have hbmin : b ≤ min a b := by omega
    refine le_trans (gCrux_le_cell a b c hbmin) ?_
    -- (a - b)(b - b) + b·c = b·c ≤ (a - s')(c - s') + s'·b  via  (a - s' − b)(c − s') ≥ 0
    rw [show b - b = 0 by omega, Nat.mul_zero, Nat.zero_add, ← Nat.cast_le (α := ℤ)]
    push_cast [Nat.cast_sub hs'a, Nat.cast_sub hs'c]
    have hcs : (0 : ℤ) ≤ (c : ℤ) - s' := by
      have : (s' : ℤ) ≤ c := by exact_mod_cast hs'c
      linarith
    have hab : (0 : ℤ) ≤ (a : ℤ) - s' - b := by
      have hba : b + s' ≤ a := by omega
      have : ((b + s' : ℕ) : ℤ) ≤ a := by exact_mod_cast hba
      push_cast at this; linarith
    nlinarith [mul_nonneg hab hcs]

/-- **The crux (symmetry).** `gCrux a b c = gCrux a c b` — the two-parameter minimum is symmetric in
its last two arguments. Both `≤`s are the single lemma `gCrux_le` (applied to `(a, b, c)` and to
`(a, c, b)`). -/
theorem gCrux_symm (a b c : ℕ) : gCrux a b c = gCrux a c b :=
  le_antisymm (gCrux_le a b c) (gCrux_le a c b)

/-- Non-vacuity: `gCrux 2 2 2 = 3` (the `(2,2,2)` anchor's front cell). -/
example : gCrux 2 2 2 = 3 := by decide

/-! ## The two-peel regroup (pure ℕ) — the abstract τ₁ symmetry -/

/-- The two-peel value `form A X Y F = ⨅_{t ≤ min A X} [(A−t)(X−t) + ⨅_{v ≤ min t Y} [(t−v)(Y−v) + F v]]`
— the value of two front-peels of a `(A, X, Y, tail)` chain, with `F` the deep-tail value. -/
def dinfForm (A X Y : ℕ) (F : ℕ → ℕ) : ℕ :=
  (Finset.range (min A X + 1)).inf' (by simp)
    (fun t => (A - t) * (X - t)
      + (Finset.range (min t Y + 1)).inf' (by simp) (fun v => (t - v) * (Y - v) + F v))

/-- **The two-peel regroup (`≤`).** `dinfForm A B C F ≤ dinfForm A C B F`. The inner-swapped form is
bounded cell-by-cell: at the RHS achiever `(t', v')`, the LHS witness `t = v' + s*` (with `s*` the
`gCrux (A−v')(B−v')(C−v')` achiever) makes the outer peel equal that `gCrux` value, which
`gCrux_symm` re-reads as `gCrux (A−v')(C−v')(B−v')` and `gCrux_le_cell` bounds by the RHS cell. -/
theorem dinfForm_le (A B C : ℕ) (F : ℕ → ℕ) : dinfForm A B C F ≤ dinfForm A C B F := by
  refine Finset.le_inf' _ _ (fun t' ht' => ?_)
  rw [Finset.mem_range] at ht'
  have ht'AC : t' ≤ min A C := by omega
  have ht'A : t' ≤ A := le_trans ht'AC (min_le_left _ _)
  have ht'C : t' ≤ C := le_trans ht'AC (min_le_right _ _)
  -- inner achiever v' of the RHS second peel.
  obtain ⟨v', hv'mem, hv'eq⟩ :=
    Finset.exists_mem_eq_inf' (s := Finset.range (min t' B + 1)) (by simp)
      (fun v => (t' - v) * (B - v) + F v)
  rw [Finset.mem_range] at hv'mem
  have hv'tB : v' ≤ min t' B := by omega
  have hv't : v' ≤ t' := le_trans hv'tB (min_le_left _ _)
  have hv'B : v' ≤ B := le_trans hv'tB (min_le_right _ _)
  have hv'A : v' ≤ A := le_trans hv't ht'A
  have hv'C : v' ≤ C := le_trans hv't ht'C
  rw [hv'eq]
  -- gCrux achiever s* of gCrux (A−v') (B−v') (C−v').
  obtain ⟨s', hs'mem, hs'eq⟩ :=
    Finset.exists_mem_eq_inf' (s := Finset.range (min (A - v') (B - v') + 1)) (by simp)
      (fun s => ((A - v') - s) * ((B - v') - s) + s * (C - v'))
  rw [Finset.mem_range] at hs'mem
  have hs'AB : s' ≤ min (A - v') (B - v') := by omega
  have hs'A : s' ≤ A - v' := le_trans hs'AB (min_le_left _ _)
  have hs'B : s' ≤ B - v' := le_trans hs'AB (min_le_right _ _)
  -- witness t = v' + s' for the LHS outer peel.
  set t := v' + s' with ht
  have htAB : t ≤ min A B := by omega
  set I := (Finset.range (min t C + 1)).inf' (by simp) (fun v => (t - v) * (C - v) + F v) with hI
  -- LHS ≤ outer cell at t.
  have houter : dinfForm A B C F ≤ (A - t) * (B - t) + I :=
    Finset.inf'_le _ (show t ∈ Finset.range (min A B + 1) by rw [Finset.mem_range]; omega)
  -- inner peel ≤ its cell at v'.
  have hinner : I ≤ (t - v') * (C - v') + F v' :=
    Finset.inf'_le _ (show v' ∈ Finset.range (min t C + 1) by rw [Finset.mem_range]; omega)
  -- the product part on the left is gCrux (A−v')(B−v')(C−v').
  have hgcell : (A - t) * (B - t) + (t - v') * (C - v')
      = gCrux (A - v') (B - v') (C - v') := by
    have hg : gCrux (A - v') (B - v') (C - v')
        = ((A - v') - s') * ((B - v') - s') + s' * (C - v') := hs'eq
    rw [hg]
    congr 1
    · congr 1 <;> omega
    · congr 1 <;> omega
  have hsymm : gCrux (A - v') (B - v') (C - v') = gCrux (A - v') (C - v') (B - v') :=
    gCrux_symm _ _ _
  have hcellC : gCrux (A - v') (C - v') (B - v') ≤ (A - t') * (C - t') + (t' - v') * (B - v') := by
    have hc := gCrux_le_cell (A - v') (C - v') (B - v') (s := t' - v') (by omega)
    calc gCrux (A - v') (C - v') (B - v')
        ≤ ((A - v') - (t' - v')) * ((C - v') - (t' - v')) + (t' - v') * (B - v') := hc
      _ = (A - t') * (C - t') + (t' - v') * (B - v') := by congr 2 <;> omega
  have hle : (A - t) * (B - t) + (t - v') * (C - v')
      ≤ (A - t') * (C - t') + (t' - v') * (B - v') := by
    rw [hgcell, hsymm]; exact hcellC
  omega

/-- **The two-peel regroup (symmetry).** `dinfForm A B C F = dinfForm A C B F` — the two-front-peel
value is symmetric in the second/third widths (with the deep tail `F` fixed). The abstract content of
the τ₁ adjacent swap. -/
theorem dinfForm_symm (A B C : ℕ) (F : ℕ → ℕ) : dinfForm A B C F = dinfForm A C B F :=
  le_antisymm (dinfForm_le A B C F) (dinfForm_le A C B F)

/-! ## The redChain-swap transport identities (peeling under an adjacent swap) -/

/-- **Deep peel.** For a `≥ 3`-width parent, an adjacent swap at positions `(k+2, k+3)` commutes with the
front-pair peel: `redChain t (M ∘ swap (k+2) (k+3)) = (redChain t M) ∘ swap (k+1) (k+2)`. The front pair
`(M₀, M₁)` is untouched (positions `≥ 2`), so peeling turns the parent τ_{k+2} into the reduced τ_{k+1}. -/
theorem redChain_comp_swap_deep {n : ℕ} (t : ℕ) (M : Fin (n + 1 + 1 + 1) → ℕ) (k : Fin n) :
    redChain t (M ∘ Equiv.swap (k.succ.succ).castSucc (k.succ.succ).succ)
      = (redChain t M) ∘ Equiv.swap (k.succ).castSucc (k.succ).succ := by
  -- move the swap through the double successor with `Matrix.cons_swap` + `map_swap`.
  have hinj : Function.Injective (fun x : Fin (n + 1) => x.succ.succ) :=
    (Fin.succ_injective _).comp (Fin.succ_injective _)
  have htail :
      (fun j : Fin (n + 1) =>
          (M ∘ Equiv.swap (k.succ.succ).castSucc (k.succ.succ).succ) j.succ.succ)
        = (fun j : Fin (n + 1) => M j.succ.succ) ∘ Equiv.swap k.castSucc k.succ := by
    funext j
    simp only [Function.comp_apply]
    have hmap := hinj.map_swap k.castSucc k.succ j
    -- hmap : (swap kc ks j).succ.succ = swap (kc.succ.succ) (ks.succ.succ) (j.succ.succ)
    have hI : (k.castSucc.succ.succ : Fin (n + 1 + 1 + 1)) = (k.succ.succ).castSucc := by
      apply Fin.ext; simp [Fin.val_succ, Fin.val_castSucc]
    congr 1
    show (Equiv.swap (k.succ.succ).castSucc (k.succ.succ).succ) j.succ.succ
        = (Equiv.swap k.castSucc k.succ j).succ.succ
    rw [hmap, hI]
  calc redChain t (M ∘ Equiv.swap (k.succ.succ).castSucc (k.succ.succ).succ)
      = Matrix.vecCons t
          (fun j : Fin (n + 1) =>
            (M ∘ Equiv.swap (k.succ.succ).castSucc (k.succ.succ).succ) j.succ.succ) := rfl
    _ = Matrix.vecCons t ((fun j : Fin (n + 1) => M j.succ.succ) ∘ Equiv.swap k.castSucc k.succ) := by
          rw [htail]
    _ = Matrix.vecCons t (fun j : Fin (n + 1) => M j.succ.succ)
          ∘ Equiv.swap (k.castSucc).succ (k.succ).succ := Matrix.cons_swap _ _ _ _
    _ = (redChain t M) ∘ Equiv.swap (k.succ).castSucc (k.succ).succ := by
          rw [Fin.succ_castSucc]; rfl

/-- **Front swap.** An adjacent swap at positions `(0, 1)` leaves the reduced chain untouched
(`redChain` reads position `0 ↦ t` and positions `≥ 2`, none of which are `0, 1`):
`redChain t (M ∘ swap 0 1) = redChain t M`. -/
theorem redChain_comp_swap_zero {n : ℕ} (t : ℕ) (M : Fin (n + 1 + 1 + 1) → ℕ) :
    redChain t (M ∘ Equiv.swap (0 : Fin (n + 1 + 1)).castSucc (0 : Fin (n + 1 + 1)).succ)
      = redChain t M := by
  funext p
  refine Fin.cases ?_ (fun q => ?_) p
  · simp [redChain]
  · simp only [redChain, Fin.cons_succ, Function.comp_apply]
    have hfix : (Equiv.swap ((0 : Fin (n + 1 + 1)).castSucc) ((0 : Fin (n + 1 + 1)).succ))
        (q.succ.succ) = q.succ.succ :=
      Equiv.swap_apply_of_ne_of_ne (by rw [Fin.castSucc_zero]; exact Fin.succ_ne_zero _)
        (fun h => Fin.succ_ne_zero q (Fin.succ_injective _ h))
    rw [hfix]

/-! ## The two-peel value of `minAdmRec` (arity ≥ 4) is `dinfForm` -/

/-- The doubly-reduced chain `(v, M₃, M₄, …)` after two front peels (independent of the first pivot). -/
def twoRed {m : ℕ} (v : ℕ) (M : Fin (m + 1 + 1 + 1 + 1) → ℕ) : Fin (m + 1 + 1) → ℕ :=
  Fin.cons v (fun i : Fin (m + 1) => M i.succ.succ.succ)

/-- Two nested front peels collapse to `twoRed` (independent of the first pivot `t`). -/
theorem redChain_redChain {m : ℕ} (t v : ℕ) (M : Fin (m + 1 + 1 + 1 + 1) → ℕ) :
    redChain v (redChain t M) = twoRed v M := by
  funext p
  induction p using Fin.cases with
  | zero => simp [redChain, twoRed]
  | succ i => simp [redChain, twoRed]

/-- **The two-peel value.** For an arity-`≥ 4` chain, `minAdmRec M = dinfForm (M₀)(M₁)(M₂) F` where the
deep tail is `F v = minAdmRec (twoRed v M)`. Two applications of `minAdmRec_succ_succ` + the redChain
identities (`redChain t M 0 = t`, `redChain t M 1 = M 2`, `redChain_redChain`). -/
theorem minAdmRec_eq_dinfForm {m : ℕ} (M : Fin (m + 1 + 1 + 1 + 1) → ℕ) :
    minAdmRec M = dinfForm (M 0) (M 1) (M 2) (fun v => minAdmRec (twoRed v M)) := by
  -- the inner (second) peel of `redChain t M`, for each `t`.
  have hinner : ∀ t : ℕ, minAdmRec (redChain t M)
      = (Finset.range (min t (M 2) + 1)).inf' (by simp)
          (fun v => (t - v) * (M 2 - v) + minAdmRec (twoRed v M)) := by
    intro t
    rw [minAdmRec_succ_succ]
    have h0 : redChain t M 0 = t := redChain_zero t M
    have h1 : redChain t M 1 = M 2 := by
      rw [show (1 : Fin (m + 1 + 1 + 1)) = (0 : Fin (m + 1 + 1)).succ from by
        apply Fin.ext; simp [Fin.val_one], redChain_succ]
      congr 1
    rw [h0, h1]
    refine Finset.inf'_congr (by simp) rfl (fun v _ => ?_)
    rw [redChain_redChain]
  rw [minAdmRec_succ_succ]
  unfold dinfForm
  refine Finset.inf'_congr (by simp) rfl (fun t _ => ?_)
  rw [hinner t]

/-- `twoRed` is unchanged by an adjacent swap at positions `(1, 2)` (it reads position `0 ↦ v` and
positions `≥ 3`, none of which are `1, 2`). -/
theorem twoRed_comp_swap_one {m : ℕ} (v : ℕ) (M : Fin (m + 1 + 1 + 1 + 1) → ℕ) :
    twoRed v (M ∘ Equiv.swap ((0 : Fin (m + 1 + 1)).succ).castSucc
        ((0 : Fin (m + 1 + 1)).succ).succ) = twoRed v M := by
  funext p
  induction p using Fin.cases with
  | zero => simp [twoRed]
  | succ i =>
      have hne1 : (i.succ.succ.succ : Fin (m + 1 + 1 + 1 + 1))
          ≠ ((0 : Fin (m + 1 + 1)).succ).castSucc := by
        apply Fin.ne_of_val_ne; simp [Fin.val_succ, Fin.val_castSucc]
      have hne2 : (i.succ.succ.succ : Fin (m + 1 + 1 + 1 + 1))
          ≠ ((0 : Fin (m + 1 + 1)).succ).succ := by
        apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_zero]; omega
      simp only [twoRed, Fin.cons_succ, Function.comp_apply,
        Equiv.swap_apply_of_ne_of_ne hne1 hne2]

/-- **Arity-3 value.** `minAdmRec (M : Fin 3) = gCrux (M 0) (M 1) (M 2)` — one peel to the two-width
leaf (`minAdmRec (redChain t M) = t · M₂`), matching `gCrux`'s definition. -/
theorem minAdmRec_three (M : Fin 3 → ℕ) : minAdmRec M = gCrux (M 0) (M 1) (M 2) := by
  have hcell : ∀ t, minAdmRec (redChain t M) = t * M 2 := by
    intro t
    rw [minAdmRec_leaf, redChain_zero]
    have h1 : redChain t M 1 = M 2 := by
      rw [show (1 : Fin 2) = (0 : Fin 1).succ from by apply Fin.ext; simp [Fin.val_one],
        redChain_succ]
      congr 1
    rw [h1]
  rw [minAdmRec_succ_succ]
  unfold gCrux
  refine Finset.inf'_congr (by simp) rfl (fun t _ => ?_)
  rw [hcell t]

/-! ## Adjacent-transposition invariance of `minAdmRec` (arity induction) -/

/-- **Adjacent-transposition invariance of `minAdmRec`.** For every chain `M : Fin (L+1) → ℕ` and every
adjacent index `i : Fin L`, `minAdmRec (M ∘ swap i.castSucc i.succ) = minAdmRec M`. By `twoStepInduction`
on `L` (mirroring `minAdmRec`): `L = 0` vacuous, `L = 1` the leaf (τ₀ manifest), and the `≥ 3`-width step
splits `i` (`Fin.cases` twice) into τ₀ (front-pair symmetry), τ₁ (the crux, via `dinfForm_symm` /
`gCrux_symm`), and the deep swap (peel + the arity-`(L−1)` induction hypothesis). -/
theorem minAdmRec_swap_adj : ∀ (L : ℕ) (M : Fin (L + 1) → ℕ) (i : Fin L),
    minAdmRec (M ∘ Equiv.swap i.castSucc i.succ) = minAdmRec M := by
  intro L
  induction L using Nat.twoStepInduction with
  | zero => intro M i; exact absurd i.2 (by omega)
  | one =>
      intro M i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rw [minAdmRec_leaf, minAdmRec_leaf]
      have e0 : (M ∘ Equiv.swap (0 : Fin 1).castSucc (0 : Fin 1).succ) 0 = M 1 := by
        rw [Function.comp_apply, Fin.castSucc_zero, Fin.succ_zero_eq_one, Equiv.swap_apply_left]
      have e1 : (M ∘ Equiv.swap (0 : Fin 1).castSucc (0 : Fin 1).succ) 1 = M 0 := by
        rw [Function.comp_apply, Fin.castSucc_zero, Fin.succ_zero_eq_one, Equiv.swap_apply_right]
      rw [e0, e1, Nat.mul_comm]
  | more n ih_n ih_n1 =>
      intro M i
      refine Fin.cases ?_ (fun i₁ => ?_) i
      · -- τ₀ : swap positions 0,1 (front-pair symmetry).
        rw [minAdmRec_succ_succ, minAdmRec_succ_succ]
        set s01 := Equiv.swap (0 : Fin (n + 1 + 1)).castSucc (0 : Fin (n + 1 + 1)).succ with hs01
        have e0 : (M ∘ s01) 0 = M 1 := by
          rw [hs01, Function.comp_apply, Fin.castSucc_zero, Fin.succ_zero_eq_one,
            Equiv.swap_apply_left]
        have e1 : (M ∘ s01) 1 = M 0 := by
          rw [hs01, Function.comp_apply, Fin.castSucc_zero, Fin.succ_zero_eq_one,
            Equiv.swap_apply_right]
        have hfin : Finset.range (min ((M ∘ s01) 0) ((M ∘ s01) 1) + 1)
            = Finset.range (min (M 0) (M 1) + 1) := by rw [e0, e1, min_comm]
        refine Finset.inf'_congr (by simp) hfin (fun t _ => ?_)
        rw [e0, e1, redChain_comp_swap_zero, Nat.mul_comm (M 1 - t) (M 0 - t)]
      · refine Fin.cases ?_ (fun k => ?_) i₁
        · -- τ₁ : swap positions 1,2 (the crux, via `gCrux_symm` / `dinfForm_symm`).
          have hA : (((0 : Fin (n + 1)).succ).castSucc : Fin (n + 1 + 1 + 1)) = 1 := by
            apply Fin.ext; simp
          have hB : (((0 : Fin (n + 1)).succ).succ : Fin (n + 1 + 1 + 1)) = 2 := by
            apply Fin.ext; simp
          have e0 : (M ∘ Equiv.swap ((0 : Fin (n + 1)).succ).castSucc
              ((0 : Fin (n + 1)).succ).succ) 0 = M 0 := by
            rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
              (Fin.ne_of_val_ne (by
                simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero]; omega))
              (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_zero]; omega))]
          have e1 : (M ∘ Equiv.swap ((0 : Fin (n + 1)).succ).castSucc
              ((0 : Fin (n + 1)).succ).succ) 1 = M 2 := by
            rw [Function.comp_apply, ← hA, Equiv.swap_apply_left, hB]
          have e2 : (M ∘ Equiv.swap ((0 : Fin (n + 1)).succ).castSucc
              ((0 : Fin (n + 1)).succ).succ) 2 = M 1 := by
            rw [Function.comp_apply, ← hB, Equiv.swap_apply_right, hA]
          rcases n with _ | m
          · -- n = 0 : arity 3, reduce both to `gCrux` and apply `gCrux_symm`.
            rw [minAdmRec_three, minAdmRec_three, e0, e1, e2]
            exact gCrux_symm (M 0) (M 2) (M 1)
          · -- n = m+1 : arity ≥ 4, reduce both to `dinfForm` and apply `dinfForm_symm`.
            have hF : (fun v => minAdmRec (twoRed v (M ∘ Equiv.swap
                  ((0 : Fin (m + 1 + 1)).succ).castSucc ((0 : Fin (m + 1 + 1)).succ).succ)))
                = (fun v => minAdmRec (twoRed v M)) := by
              funext v; rw [twoRed_comp_swap_one]
            rw [minAdmRec_eq_dinfForm, minAdmRec_eq_dinfForm, e0, e1, e2, hF,
              dinfForm_symm (M 0) (M 2) (M 1)]
        · -- deep : swap positions k+2,k+3 (peel + IH at arity n+1).
          rw [minAdmRec_succ_succ, minAdmRec_succ_succ]
          set sd := Equiv.swap (k.succ.succ).castSucc (k.succ.succ).succ with hsd
          have hA0 : (0 : Fin (n + 1 + 1 + 1)) ≠ (k.succ.succ).castSucc := by
            apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero]; omega
          have hB0 : (0 : Fin (n + 1 + 1 + 1)) ≠ (k.succ.succ).succ := by
            apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_zero]; omega
          have hA1 : (1 : Fin (n + 1 + 1 + 1)) ≠ (k.succ.succ).castSucc := by
            apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_one]; omega
          have hB1 : (1 : Fin (n + 1 + 1 + 1)) ≠ (k.succ.succ).succ := by
            apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_one]; omega
          have e0 : (M ∘ sd) 0 = M 0 := by
            rw [hsd, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hA0 hB0]
          have e1 : (M ∘ sd) 1 = M 1 := by
            rw [hsd, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hA1 hB1]
          have hfin : Finset.range (min ((M ∘ sd) 0) ((M ∘ sd) 1) + 1)
              = Finset.range (min (M 0) (M 1) + 1) := by rw [e0, e1]
          refine Finset.inf'_congr (by simp) hfin (fun t _ => ?_)
          rw [e0, e1, hsd, redChain_comp_swap_deep, ih_n1 (redChain t M) (k.succ)]

/-- Adjacent-transposition invariance transferred to `minAdm` (`= minAdmRec`). -/
theorem minAdm_swap_adj {L : ℕ} (M : Fin (L + 1) → ℕ) (i : Fin L) :
    minAdm (M ∘ Equiv.swap i.castSucc i.succ) = minAdm M := by
  rw [← minAdmRec_eq_minAdm, ← minAdmRec_eq_minAdm, minAdmRec_swap_adj]

/-! ## Full permutation-invariance of `minAdm` -/

/-- **`minAdm` is permutation-invariant.** `minAdm (M ∘ σ) = minAdm M` for every permutation `σ` of the
entries. The invariant permutations form a submonoid containing every adjacent transposition
(`minAdm_swap_adj`); adjacent transpositions generate `Sₙ`
(`Equiv.Perm.mclosure_swap_castSucc_succ`), so the submonoid is everything. -/
theorem minAdm_comp_perm {L : ℕ} (σ : Equiv.Perm (Fin (L + 1))) (M : Fin (L + 1) → ℕ) :
    minAdm (M ∘ σ) = minAdm M := by
  -- the submonoid of `minAdm`-invariant permutations (quantified over ALL chains).
  let H : Submonoid (Equiv.Perm (Fin (L + 1))) :=
    { carrier := {σ | ∀ M : Fin (L + 1) → ℕ, minAdm (M ∘ σ) = minAdm M}
      one_mem' := by intro M; simp
      mul_mem' := by
        intro a b ha hb M
        have hcomp : M ∘ ⇑(a * b) = (M ∘ ⇑a) ∘ ⇑b := by rw [Equiv.Perm.coe_mul]; rfl
        rw [hcomp, hb (M ∘ ⇑a), ha M] }
  have hsub : Submonoid.closure (Set.range fun i : Fin L ↦ Equiv.swap i.castSucc i.succ) ≤ H :=
    Submonoid.closure_le.2 (by rintro _ ⟨i, rfl⟩ M; exact minAdm_swap_adj M i)
  have hσ : σ ∈ H := by
    apply hsub
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top σ
  exact hσ M

/-- **`minAdm` is invariant under sorting** (the specialization Part 2 consumes): `minAdm` on any chain
equals `minAdm` on its monotone rearrangement `M ∘ Tuple.sort M`. -/
theorem minAdm_comp_sort {L : ℕ} (M : Fin (L + 1) → ℕ) :
    minAdm (M ∘ _root_.Tuple.sort M) = minAdm M :=
  minAdm_comp_perm (_root_.Tuple.sort M) M

/-- Non-vacuity: `minAdm` agrees on the non-monotone `(2,3,2)` and its sorted form `(2,2,3)` (the swap
`(1 2)`), both `= 4`. -/
example : minAdm (![2, 3, 2] : Fin 3 → ℕ) = minAdm (![2, 2, 3] : Fin 3 → ℕ) := by
  have h : (![2, 2, 3] : Fin 3 → ℕ) = (![2, 3, 2] : Fin 3 → ℕ) ∘ Equiv.swap 1 2 := by decide
  rw [h, minAdm_comp_perm]

end DLNFibre.DLN.RLCT
