import DLNFibre.DLN.RLCT.Validate.RouteMDeepBottleneck
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedMinAdm

/-!
# `RouteMSmearedWaist` — the width-`r` waist for a boundary-smeared `M` (item 2)

The KEY structural input to the general-`L` smeared box supplier: a front layer `q ≤ L−1` whose width
`M ⟨q⟩` equals the deepest rank `deepRank M = r`, together with the fact that `r` is a LOWER BOUND on
every FRONT width `M ⟨t⟩` (`t < L`). This is exactly the `hMq` (`M ⟨q⟩ = r`) + `hwidth`
(`∀ t < L, r ≤ M ⟨t⟩`) the carrier-corridor machinery (`wideCarrierBound_suffix`,
`waist_carrier_data`) consumes.

## Soundness note (carried next to the claim)
The width lower bound is over the FRONT layers `t < L` ONLY — NOT `t = L`. The deepest width `M ⟨L⟩`
is genuinely NOT bounded below by `deepRank` for a smeared `M` (counterexample `M = (2,3,1)`:
`deepRank = 2`, `M ⟨2⟩ = 1`). This is fine: the carrier corridor lives in `frontProd = prodAux (L−1)`,
which only reads front layers `0..L−1`; the deepest factor `M ⟨L⟩` is never in it. Numerically verified
0-fails for the front form (L ∈ {2,3,4}, widths 1..5).

## The proof (adjudicator, Codex-reconciled)
* **(A) `∀ t < L, deepRank ≤ M ⟨t⟩`** — `deepRank = Text (tach) L`, weakly decreasing (`structAdm`'s
  `hdesc` + the identity boundary `Text 0 = Text 1`), so `Text L ≤ Text (t+1) ≤ Wext t = M ⟨t⟩` (the
  per-layer bound `hc`/`hub`, for `t < L`), and `Text L ≤ Text 0 = M 0` at `t = 0`. Universal — needs
  only admissibility, not smearedness.
* **(B) `∃ q ≤ L−1, M ⟨q⟩ = deepRank`** — the descent bottoms out: `Text` weakly decreases from
  `Text 1 = M 0` to `Text L = deepRank`, each step `Text (k+2) ≤ Wext (k+1) = M ⟨k+1⟩`; and the LAST
  step's target `Wext (L−1) = deepRows > deepRank` (smeared) forces the minimum `deepRank` to be
  ATTAINED at a front layer strictly before `L`. Concretely: the front-width minimum equals `deepRank`
  (both `≤` by (A) and `≥` because `Text` never drops below a width it passed through).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## `Text (tach)` weak monotonicity (the descent is weakly decreasing) -/

/-- **`Text (tach) 0 = Text (tach) 1`** — the identity boundary (`Text 0 = M 0 = tach 0 = Text 1`). -/
theorem Text_tach_zero_eq_one (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    Text M (tach M) 0 = Text M (tach M) 1 := by
  rw [Text_zero, Text_tach_succ M 0 (by omega), tach_mk_zero M (by omega)]

/-- **`Text (tach) (k+1) ≤ Text (tach) k`** for `k ≤ L` — one step of weak decrease. At `k = 0` the
identity boundary; at `k = j+1` the achiever descent (`structAdm`'s `hdesc`). -/
theorem Text_tach_step_le (M : Fin (L + 1) → ℕ) (hL : 0 < L) (k : ℕ) (hk : k ≤ L) :
    Text M (tach M) (k + 1) ≤ Text M (tach M) k := by
  match k with
  | 0 => rw [← Text_tach_zero_eq_one M hL]
  | (j + 1) =>
      have hjL : j < L := by omega
      exact (structAdm_tach M hL).hdesc j hjL

/-- **`Text (tach)` is weakly decreasing** (`i ≤ j ≤ L ⟹ Text j ≤ Text i`), by induction on the gap. -/
theorem Text_tach_antitone (M : Fin (L + 1) → ℕ) (hL : 0 < L) {i j : ℕ}
    (hij : i ≤ j) (hjL : j ≤ L) : Text M (tach M) j ≤ Text M (tach M) i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ j hij ih =>
      have hjL' : j ≤ L := by omega
      exact le_trans (Text_tach_step_le M hL j hjL') (ih hjL')

/-! ## Part (A): the front-width lower bound `∀ t < L, deepRank ≤ M ⟨t⟩` -/

/-- **The per-layer bound `Text (tach) (t+1) ≤ M ⟨t⟩`** for `t < L` (`Wext t = M ⟨t⟩`). For `t = 0`:
`Text 1 = M 0`; for `t = k+1`: `Text (k+2) ≤ Wext (k+1) = M ⟨k+1⟩` (`structAdm`'s `hub`). -/
theorem Text_tach_succ_le_M (M : Fin (L + 1) → ℕ) (hL : 0 < L) (t : ℕ) (ht : t < L) :
    Text M (tach M) (t + 1) ≤ M ⟨t, by omega⟩ := by
  match t with
  | 0 =>
      rw [Text_tach_succ M 0 (by omega), tach_mk_zero M (by omega)]
      exact le_of_eq (by congr 1)
  | (k + 1) =>
      have := (structAdm_tach M hL).hub k
      rwa [Wext_apply M (k + 1) (by omega)] at this

/-- **Part (A): `∀ t < L, deepRank M ≤ M ⟨t⟩`** — the FRONT-width lower bound. `deepRank = Text L ≤
Text (t+1) ≤ M ⟨t⟩` (weak decrease + the per-layer bound). Universal (admissibility only). -/
theorem deepRank_le_M_front (M : Fin (L + 1) → ℕ) (hL : 0 < L) (t : ℕ) (ht : t < L) :
    deepRank M ≤ M ⟨t, by omega⟩ := by
  have h1 : Text M (tach M) L ≤ Text M (tach M) (t + 1) :=
    Text_tach_antitone M hL (by omega) (by omega)
  have h2 : Text M (tach M) (t + 1) ≤ M ⟨t, by omega⟩ := Text_tach_succ_le_M M hL t ht
  rw [deepRank]; exact le_trans h1 h2

/-! ## Part (B): the waist index `∃ q ≤ L−1, M ⟨q⟩ = deepRank`

The MINIMAL-index argument (Codex-reconciled): let `k₀` be the least `k ≤ L` with `Text k = deepRank`
(exists, `Text L = deepRank`). If `k₀ = 0`: `deepRank = Text 0 = Text 1 = M 0` (identity boundary), waist
`q = 0`. If `k₀ ≥ 1`: `Text k₀ = deepRank` but `Text (k₀−1) > deepRank` (minimality), a genuine ROW drop
at chain boundary `s = k₀−1 ∈ [1, L−1]`. `NoInteriorBothDrop` at `s` forbids BOTH drops, so the COLUMN
does not drop: `¬ (Text s < Wext(s−1))`... actually the vanishing `rBlock (s−1)·cBlock (s−1) = 0` with
`rBlock > 0` (row drop) forces `cBlock = 0`, i.e. `Wext(s−1) = Text s = deepRank`, waist `q = s−1`.

This rests on `NoInteriorBothDrop` (the interior Aoyagi blocks vanish) — the same hypothesis
`minAdm_eq_deepRank_mul_last` and the whole smeared/clean chart assembly carry. The smeared `<` is NOT
needed for attainment (holds under `NoInteriorBothDrop` + `0 < L` alone). -/

/-- **The waist index `∃ q ≤ L−1, M ⟨q⟩ = deepRank`.** Least `k` with `Text k = deepRank` (exists,
`k = L`). `k₀ = 0` ⟹ `M 0 = deepRank` (waist `q = 0`). `k₀ = 1` is impossible (identity boundary
`Text 0 = Text 1` would give `k₀ = 0`). `k₀ ≥ 2` ⟹ the row drop `Text (k₀−1) > Text k₀ = deepRank` at
chain boundary `j = ⟨k₀−2⟩` (`rBlock j = Text(k₀−1) − Text k₀ > 0`) forces, by `NoInteriorBothDrop`'s
vanishing `rBlock j · cBlock j = 0`, `cBlock j = M(k₀−1) − Text k₀ = 0`, i.e. `M(k₀−1) = deepRank`
(waist `q = k₀−1`). The vanishing needs `j.val = k₀−2 < L−1`, i.e. `k₀ ≤ L` (given). -/
theorem exists_waist_eq_deepRank (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hNo : NoInteriorBothDrop M) :
    ∃ q : ℕ, q ≤ L - 1 ∧ ∃ hq : q < L + 1, M ⟨q, hq⟩ = deepRank M := by
  -- the least `k` with `Text k = deepRank` (exists: `k = L`)
  have hex : ∃ k, Text M (tach M) k = deepRank M := ⟨L, rfl⟩
  classical
  set k₀ := Nat.find hex with hk₀def
  have hk₀ : Text M (tach M) k₀ = deepRank M := Nat.find_spec hex
  have hk₀L : k₀ ≤ L := Nat.find_min' hex (rfl : Text M (tach M) L = deepRank M)
  -- `k₀ ≠ 1`: else `Text 0 = Text 1 = deepRank`, so `0` is in the set, contradicting minimality.
  have hk₀ne1 : k₀ ≠ 1 := by
    intro h1
    have h0 : Text M (tach M) 0 = deepRank M := by
      rw [Text_tach_zero_eq_one M hL, ← h1]; exact hk₀
    exact absurd h0 (Nat.find_min hex (m := 0) (by omega))
  rcases Nat.eq_zero_or_pos k₀ with hz | hpos
  · -- `k₀ = 0`: `deepRank = Text 0 = M 0`, waist `q = 0`
    refine ⟨0, by omega, by omega, ?_⟩
    have h0 : Text M (tach M) 0 = deepRank M := by rw [← hk₀, hz]
    rw [Text_zero] at h0
    rw [show (⟨0, by omega⟩ : Fin (L + 1)) = 0 from rfl]; exact h0
  · -- `k₀ ≥ 2`: the row drop at chain boundary `j = ⟨k₀−2⟩`
    have hk₀2 : 2 ≤ k₀ := by omega
    -- `Text (k₀−1) ≠ deepRank` (minimality) with `Text (k₀−1) ≥ Text k₀ = deepRank` ⟹ strict `>`
    have hprev_ne : Text M (tach M) (k₀ - 1) ≠ deepRank M :=
      Nat.find_min hex (m := k₀ - 1) (by omega)
    have hprev_ge : Text M (tach M) k₀ ≤ Text M (tach M) (k₀ - 1) := by
      have hkk : k₀ - 1 + 1 = k₀ := by omega
      calc Text M (tach M) k₀ = Text M (tach M) ((k₀ - 1) + 1) := by rw [hkk]
        _ ≤ Text M (tach M) (k₀ - 1) := Text_tach_step_le M hL (k₀ - 1) (by omega)
    have hrow : Text M (tach M) k₀ < Text M (tach M) (k₀ - 1) := by
      rw [hk₀] at hprev_ge ⊢; omega
    -- the interior boundary `j = ⟨k₀−2,_⟩ : Fin L`; `j.val + 1 = k₀−1`, `j.val + 2 = k₀`
    have hjlt : k₀ - 2 < L := by omega
    set j : Fin L := ⟨k₀ - 2, hjlt⟩ with hjdef
    have hjLm1 : j.val < L - 1 := by simp only [hjdef]; omega
    have hvanish := rBlock_cBlock_interior_eq_zero M hNo j hjLm1
    rw [rBlock_eq_Text, cBlock_eq_Wext] at hvanish
    have hj1 : j.val + 1 = k₀ - 1 := by simp only [hjdef]; omega
    have hj2 : j.val + 2 = k₀ := by simp only [hjdef]; omega
    rw [hj1, hj2] at hvanish
    -- `hvanish : (Text (k₀−1) − Text k₀) · (Wext (k₀−1) − Text k₀) = 0` over ℤ; row factor > 0.
    have hrowZ : (0 : ℤ) < (Text M (tach M) (k₀ - 1) : ℤ) - (Text M (tach M) k₀ : ℤ) := by
      have : (Text M (tach M) k₀ : ℤ) < (Text M (tach M) (k₀ - 1) : ℤ) := by exact_mod_cast hrow
      linarith
    have hcolZ : (Wext M (k₀ - 1) : ℤ) - (Text M (tach M) k₀ : ℤ) = 0 := by
      rcases mul_eq_zero.mp hvanish with h | h
      · exact absurd h (by linarith [hrowZ])
      · exact h
    -- `Wext (k₀−1) = Text k₀ = deepRank`, and `Wext (k₀−1) = M ⟨k₀−1,_⟩`
    have hWq : Wext M (k₀ - 1) = deepRank M := by
      have : (Wext M (k₀ - 1) : ℤ) = (Text M (tach M) k₀ : ℤ) := by linarith [hcolZ]
      rw [← hk₀]; exact_mod_cast this
    refine ⟨k₀ - 1, by omega, by omega, ?_⟩
    rw [Wext_apply M (k₀ - 1) (by omega)] at hWq
    exact hWq

/-! ## The packaged waist lemma (the `hMq` + `hwidth` the box supplier consumes) -/

/-- **THE width-`r` waist for a boundary `M`** (`r = deepRank M`), under `NoInteriorBothDrop` (the same
hypothesis the smeared/clean chart assembly + `minAdm_eq_deepRank_mul_last` carry). Produces the waist
index `q ≤ L−1` with `M ⟨q⟩ = deepRank M`, together with the FRONT-width lower bound `∀ t < L, deepRank
≤ M ⟨t⟩` — exactly the `hMq`/`hwidth` inputs the carrier-corridor det machinery consumes. -/
theorem smeared_waist (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hNo : NoInteriorBothDrop M) :
    ∃ q : ℕ, ∃ hq : q < L + 1, q ≤ L - 1 ∧ M ⟨q, hq⟩ = deepRank M
      ∧ (∀ t : ℕ, t < L → deepRank M ≤ Wext M t) := by
  obtain ⟨q, hqL, hqLt, hMq⟩ := exists_waist_eq_deepRank M hL hNo
  refine ⟨q, by omega, hqL, ?_, ?_⟩
  · exact hMq
  · intro t ht
    rw [Wext_apply M t (by omega)]
    exact deepRank_le_M_front M hL t ht

end DLNFibre.DLN.RLCT
