import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Validate.ResolutionAtlas

/-!
# `RouteMAchieverPath` — the ∀M achiever descent path `tStar M` + the radial active count

Step 1 of the ∀M R1-lower lift (the (2,2,2) `tach222` made width-parametric). The achiever chart for
arbitrary `M` blows up the codim-`minAdm M` achiever center radially at one pivot. The `minAdm`
normal directions are the per-boundary residual blocks of a fixed `Mval`-minimizer `T*` (the achiever
descent path), with `active.card = ∑_j r_j·c_j = minAdm M` — DEFINITIONAL (`minAdm = min Mval`,
`Mval M T = ∑_j r_j·c_j`), per `threads/36-…/certificate-achiever-path.md` (KC1).

* `Mval_nonneg_adm` — `0 ≤ Mval M T` on the admissible cone (each summand `r_j·c_j ≥ 0`).
* `tStar M` — a CHOSEN `Mval`-minimizer (`Classical.choose` of the attaining `inf'` witness); the
  achiever descent path. `tStar_mem`, `Mval_tStar_eq : Mval M (tStar M) = minAdm M`.
* `rBlock` / `cBlock` — the per-boundary residual block dimensions (`r_j = t^{j−1}−t^j`,
  `c_j = M_{j+1}−t^j`, the AFTER-width `c`).
* `sum_rBlock_cBlock_eq_minAdm` — `∑_j r_j·c_j = minAdm M` (the load-bearing `active.card` identity).

Axiom-clean modulo `Classical.choice` (the minimizer choice) `[propext, Classical.choice, Quot.sound]`.

REGRESSION (specialize-and-check): `tStar` is a chosen minimizer, so `tStar M222` need not be the
literal `tach222`; what is checked is the INVARIANT `Mval M (tStar M) = minAdm M` on every anchor.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## `Mval ≥ 0` on the admissible cone -/

/-- The predecessor exponent dominates the current on the admissible cone: `T j ≤ tPrev M T j`
(weak-decrease `t⁽¹⁾ ≥ … ≥ t⁽ᴸ⁾`, with `t⁽⁰⁾ = M 0 ≥ t⁽¹⁾` since `t⁽¹⁾ ≤ min(M 0, M 1)`). -/
theorem tStar_le_tPrev (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    (T j : ℤ) ≤ tPrev M T j := by
  obtain ⟨hbound, hdec, _⟩ := (Finset.mem_filter.1 hT).2
  unfold tPrev
  by_cases hj0 : j.val = 0
  · rw [if_pos hj0]
    have hb := hbound j
    rw [admBound, if_pos hj0] at hb
    have : T j ≤ M 0 := le_trans hb (min_le_left _ _)
    exact_mod_cast this
  · rw [if_neg hj0]
    have hpred : (⟨j.val - 1, by omega⟩ : Fin L) ≤ j := by
      simp only [Fin.le_def]; omega
    exact_mod_cast hdec ⟨j.val - 1, by omega⟩ j hpred

/-- The residual width is nonneg on the admissible cone: `T j ≤ M_{j+1}` (the `admBound`). -/
theorem tStar_le_Msucc (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    (T j : ℤ) ≤ (M j.succ : ℤ) := by
  obtain ⟨hbound, _, _⟩ := (Finset.mem_filter.1 hT).2
  have hb := hbound j
  by_cases hj0 : j.val = 0
  · rw [admBound, if_pos hj0] at hb
    have : T j ≤ M 1 := le_trans hb (min_le_right _ _)
    have hL : 0 < L := j.pos
    have hsucc : M j.succ = M 1 := by
      congr 1; apply Fin.ext
      rw [Fin.val_succ, hj0, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [hsucc]; exact_mod_cast this
  · rw [admBound, if_neg hj0] at hb
    exact_mod_cast hb

/-- `0 ≤ (Adm M).inf' Mval` (the min over the nonempty admissible cone of nonneg values; `Mval ≥ 0` on
`Adm` is the banked `ResolutionAtlas.Mval_nonneg_adm`). -/
theorem inf'_Mval_nonneg (M : Fin (L + 1) → ℕ) :
    0 ≤ (Adm M).inf' (Adm_nonempty M) (Mval M) := by
  rw [Finset.le_inf'_iff]
  exact fun T hT => Mval_nonneg_adm M T hT

/-! ## The chosen achiever descent path `tStar M` -/

/-- The attaining-witness existence: some `T ∈ Adm M` realises the `inf'`. -/
theorem exists_tStar (M : Fin (L + 1) → ℕ) :
    ∃ T ∈ Adm M, Mval M T = (Adm M).inf' (Adm_nonempty M) (Mval M) := by
  obtain ⟨T, hT, heq⟩ := (Adm M).exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
  exact ⟨T, hT, heq.symm⟩

/-- **The chosen `Mval`-minimizer** `tStar M` — the achiever descent path (`Classical.choose` of the
attaining witness; any argmin works, the chart invariants are minimizer-independent per the cert). -/
noncomputable def tStar (M : Fin (L + 1) → ℕ) : Fin L → ℕ :=
  (exists_tStar M).choose

/-- `tStar M ∈ Adm M`. -/
theorem tStar_mem (M : Fin (L + 1) → ℕ) : tStar M ∈ Adm M :=
  (exists_tStar M).choose_spec.1

/-- `Mval M (tStar M) = (Adm M).inf' Mval` (the attaining identity). -/
theorem Mval_tStar_eq_inf' (M : Fin (L + 1) → ℕ) :
    Mval M (tStar M) = (Adm M).inf' (Adm_nonempty M) (Mval M) :=
  (exists_tStar M).choose_spec.2

/-- **`Mval M (tStar M) = minAdm M`** (over ℤ): the achiever path realises the minimal admissible codim.
`minAdm = (inf' Mval).toNat`, and `inf' Mval ≥ 0`, so the `toNat` round-trips. -/
theorem Mval_tStar_eq (M : Fin (L + 1) → ℕ) : Mval M (tStar M) = (minAdm M : ℤ) := by
  rw [Mval_tStar_eq_inf', minAdm, Int.toNat_of_nonneg (inf'_Mval_nonneg M)]

/-! ## The per-boundary residual blocks (`r_j × c_j`) + `∑ r_j·c_j = minAdm` -/

/-- The rows dropped at boundary `j`: `r_j = t⁽ʲ⁻¹⁾ − t⁽ʲ⁾` (`t⁽⁰⁾ = M 0`). The achiever-center normal
block's row count at boundary `j`. -/
noncomputable def rBlock (M : Fin (L + 1) → ℕ) (j : Fin L) : ℤ := tPrev M (tStar M) j - (tStar M j : ℤ)

/-- The residual columns at boundary `j`: `c_j = M_{j+1} − t⁽ʲ⁾` (the Aoyagi AFTER-width). -/
noncomputable def cBlock (M : Fin (L + 1) → ℕ) (j : Fin L) : ℤ := (M j.succ : ℤ) - (tStar M j : ℤ)

/-- `0 ≤ rBlock` (weak-decrease) and `0 ≤ cBlock` (admBound). -/
theorem rBlock_nonneg (M : Fin (L + 1) → ℕ) (j : Fin L) : 0 ≤ rBlock M j := by
  unfold rBlock; linarith [tStar_le_tPrev M (tStar M) (tStar_mem M) j]

theorem cBlock_nonneg (M : Fin (L + 1) → ℕ) (j : Fin L) : 0 ≤ cBlock M j := by
  unfold cBlock; linarith [tStar_le_Msucc M (tStar M) (tStar_mem M) j]

/-- **`∑_j r_j·c_j = minAdm M`** — the load-bearing `active.card` identity (the radial blow-up of the
achiever center has exactly `minAdm` normal directions, one per residual-block entry). DEFINITIONAL:
`Mval M (tStar M) = ∑_j (tPrev − t_j)(M_{j+1} − t_j) = ∑_j r_j·c_j`, and `Mval (tStar) = minAdm`. -/
theorem sum_rBlock_cBlock_eq_minAdm (M : Fin (L + 1) → ℕ) :
    ∑ j : Fin L, rBlock M j * cBlock M j = (minAdm M : ℤ) := by
  rw [← Mval_tStar_eq M]
  unfold Mval rBlock cBlock
  rfl

end DLNFibre.DLN.RLCT
