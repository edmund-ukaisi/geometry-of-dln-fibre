import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

/-!
# `DLNFibre.DLN.RLCT.Foundations.Lambda` — Aoyagi's closed-form learning coefficient

The candidate value `Mval`, the admissible cone `Adm`, the core `lambdaCore = ½·min_T M(T)`,
the closed form `aoyagiLambda`, and the order `aoyagiTheta = a(ℓ−a)+1` (design-spec §4).

`aoyagiLambda` is defined **via the minimisation** `½·min_{T ∈ Adm} M(T)` — total and
Def-3-free (controller standing decision 3; the printed Theorem-2 form and the clean form are
proven equal where Def 3 applies, as the A1 lemmas). The naive "extremise the clean form over
ℓ" is WRONG: `min_ℓ` can go negative (`M=(1,1,1,4)` → −1/2) and `max_ℓ` mis-selects
(`M=(2,2,2)`: Def-3 ℓ=2 → 3/2, `max_ℓ` ℓ=1 → 2); verified in the design spec §4.3. The
minimisation is the faithful total object; the clean form is its *value* at the genuine minimiser.

Spelled with Lean-safe names (`λ` is reserved): `aoyagiLambda` is Aoyagi's `λ`, `aoyagiTheta`
his `θ`.

Ground truth (design-spec §5), enforced by the `#guard_msgs`/`#eval` checks below:
`(2,2,2)→3/2`, `(2,1,2)→1`, `(2,2,2,2)→3/2`, `(3,3,3,3)→3`.
-/

namespace DLNFibre.DLN.RLCT

open Finset

variable {L : ℕ}

/-- `t⁽ʲ⁻¹⁾` with the convention `t⁽⁰⁾ := M⁽¹⁾ = M 0` (which unifies the first term of `M(T)`
with the sum; design-spec §4.1). For `j : Fin L` the predecessor exponent. -/
def tPrev (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) : ℤ :=
  if j.val = 0 then (M 0 : ℤ) else (T ⟨j.val - 1, by omega⟩ : ℤ)

/-- Aoyagi's candidate RLCT-contribution value (design-spec §4.1, transcribed from Aoyagi p.22):
`M(T) = (M⁽¹⁾−t⁽¹⁾)(M⁽²⁾−t⁽¹⁾) + ∑_{j=2}^L (t⁽ʲ⁻¹⁾−t⁽ʲ⁾)(M⁽ʲ⁺¹⁾−t⁽ʲ⁾)`, written as the single sum
`∑_{j=1}^L (t⁽ʲ⁻¹⁾−t⁽ʲ⁾)(M⁽ʲ⁺¹⁾−t⁽ʲ⁾)` with `t⁽⁰⁾ := M⁽¹⁾`. Over ℤ (the factors are signed). -/
def Mval (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : ℤ :=
  ∑ j : Fin L, (tPrev M T j - (T j : ℤ)) * ((M j.succ : ℤ) - (T j : ℤ))

/-- Per-layer upper bound on `t⁽ʲ⁾`: `min(M⁽¹⁾,M⁽²⁾)` for `j = 1`, else `M⁽ʲ⁺¹⁾`
(design-spec §4.1). -/
def admBound (M : Fin (L + 1) → ℕ) (j : Fin L) : ℕ :=
  if j.val = 0 then min (M 0) (M 1) else M j.succ

/-- Admissibility (design-spec §4.1): weak-decrease `t⁽¹⁾ ≥ … ≥ t⁽ᴸ⁾`, last exponent `t⁽ᴸ⁾ = 0`, and
each `t⁽ʲ⁾` within its block bound. The genuine admissible cone the blow-up realises. -/
def admPred (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Prop :=
  (∀ j : Fin L, T j ≤ admBound M j) ∧
  (∀ i j : Fin L, i ≤ j → T j ≤ T i) ∧
  (∀ j : Fin L, j.val = L - 1 → T j = 0)

instance (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Decidable (admPred M T) := by
  unfold admPred; infer_instance

/-- The finite admissible cone of exponent vectors `T` (design-spec §4.1). Finite because each
`t⁽ʲ⁾` ranges over `0..admBound`, so `min_T M(T)` exists unconditionally — making `aoyagiLambda`
total. -/
def Adm (M : Fin (L + 1) → ℕ) : Finset (Fin L → ℕ) :=
  (Fintype.piFinset (fun j => Finset.range (admBound M j + 1))).filter (admPred M)

/-- The all-zeros exponent vector is admissible (so `Adm` is nonempty). -/
theorem zero_mem_Adm (M : Fin (L + 1) → ℕ) : (fun _ => 0) ∈ Adm M := by
  rw [Adm, mem_filter]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]; intro j; rw [mem_range]; omega
  · intro j; exact Nat.zero_le _
  · intro i j _; exact le_refl 0
  · intro j _; rfl

/-- `Adm M` is nonempty (the all-zeros vector witnesses it; design-spec §4.2). -/
theorem Adm_nonempty (M : Fin (L + 1) → ℕ) : (Adm M).Nonempty :=
  ⟨_, zero_mem_Adm M⟩

/-- `λ_core = ½·min_{T ∈ Adm} M(T)` (design-spec §4.2). Total via `Finset.inf'` over the nonempty
finite `Adm M`; the clean closed form `¼(Σqᵢ² − Σmₖ²)` is proven equal as A1, not baked in here. -/
def lambdaCore (M : Fin (L + 1) → ℕ) : ℚ :=
  (1 / 2 : ℚ) * ((Adm M).inf' (Adm_nonempty M) (Mval M) : ℤ)

/-- Aoyagi's learning coefficient `λ = [−r² + r(H⁽¹⁾+H⁽ᴸ⁺¹⁾)]/2 + λ_core` (design-spec §4.2), the
regular-part shift plus the singular-core minimisation over the reduced widths `M⁽ˢ⁾ = H⁽ˢ⁾ − r`.
Total and Def-3-free. (`λ` is reserved in Lean; this is Aoyagi's `λ`.) -/
def aoyagiLambda (H : Fin (L + 1) → ℕ) (r : ℕ) : ℚ :=
  (-(r : ℚ) ^ 2 + r * (H 0 + H (Fin.last L))) / 2 + lambdaCore (fun s => H s - r)

/-- Aoyagi's order `θ = a(ℓ−a)+1` (design-spec §3; Aoyagi Theorem 2). The combinatorial
deliverable, total in the Def-3 data `(ℓ, a)`. The binding of `(ℓ, a)` to `(H, r)` rides with
Def-3 (A2); θ is **not** the naive count of minimisers of `M(T)` (design-spec §3 seam). -/
def aoyagiTheta (ℓ a : ℕ) : ℕ := a * (ℓ - a) + 1

-- Ground-truth cross-check (design-spec §5; all reproduce exactly, enforced at build time).
/-- info: 3 / 2 -/
#guard_msgs in
#eval aoyagiLambda (![2, 2, 2] : Fin 3 → ℕ) 0
/-- info: 1 -/
#guard_msgs in
#eval aoyagiLambda (![2, 1, 2] : Fin 3 → ℕ) 0
/-- info: 3 / 2 -/
#guard_msgs in
#eval aoyagiLambda (![2, 2, 2, 2] : Fin 4 → ℕ) 0
/-- info: 3 -/
#guard_msgs in
#eval aoyagiLambda (![3, 3, 3, 3] : Fin 4 → ℕ) 0
/-- info: 2 -/
#guard_msgs in
#eval aoyagiTheta 2 1

/-! ## Zero reduced width: the arithmetic collapse `lambdaCore = 0`

Aoyagi's theorem covers reduced widths `= 0` (worked.tex:670,710-711 — the `ℓ+1` smallest reduced
widths, possibly `0`; `P = Σ` with no positivity). At any zero reduced width the singular core
contributes nothing. This is the **arithmetic** half (elder charge-8 (ii)); the *analytic*
layer-collapse (a zero-width layer reducing the depth `L`) is separate and not proven here.

`lambdaCore M = 0 ⟺ ∃ s, M s = 0` was brute-forced exhaustively (`L ≤ 4`, widths `0..5`); the
forward direction below is the library-completeness win (the value theorems' `hpos : ∀ s, r < H s`
narrowing; the DLN destination supplies `hpos` free, so this is off its critical path). -/

/-- When `j = 0` the successor index is `1`; used to identify `M j.succ` with `M 1`. -/
theorem succ_eq_one_of_val_zero (j : Fin L) (h : j.val = 0) : j.succ = (1 : Fin (L + 1)) := by
  have hL : 0 < L := by have := j.isLt; omega
  have h1 : ((1 : Fin (L + 1)) : ℕ) = 1 :=
    (Fin.val_one' (L + 1)).trans (Nat.mod_eq_of_lt (by omega))
  apply Fin.ext
  rw [Fin.val_succ, h]
  omega

/-- `admBound M j ≤ M^{j+1}`: at `j = 0` it is `min(M⁰,M¹) ≤ M¹ = M^{j+1}`; else it is `M^{j+1}`. -/
theorem admBound_le_Msucc (M : Fin (L + 1) → ℕ) (j : Fin L) : admBound M j ≤ M j.succ := by
  unfold admBound
  split
  · next h => rw [succ_eq_one_of_val_zero j h]; exact min_le_right _ _
  · next h => exact le_refl _

/-- Every summand of `Mval` is a product of two nonnegatives on the admissible cone, so `Mval ≥ 0`
there: `tPrev − Tⱼ ≥ 0` (weak-decrease, and `T₀ ≤ min(M⁰,M¹) ≤ M⁰`) and `M^{j+1} − Tⱼ ≥ 0`
(`Tⱼ ≤ admBound ≤ M^{j+1}`). -/
theorem Mval_nonneg_of_mem_Adm (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    0 ≤ Mval M T := by
  rw [Adm, mem_filter] at hT
  obtain ⟨-, hbound, hdec, -⟩ := hT
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg
  · -- `0 ≤ tPrev M T j − T j`
    rw [sub_nonneg]
    unfold tPrev
    split
    · -- `j.val = 0`: `tPrev = M 0 ≥ T 0`
      next h =>
        have hb := hbound j
        unfold admBound at hb
        rw [if_pos h] at hb
        exact_mod_cast le_trans hb (min_le_left _ _)
    · -- `j.val ≠ 0`: `tPrev = T ⟨j-1⟩ ≥ T j` by weak-decrease
      next h =>
        have : T j ≤ T ⟨j.val - 1, by omega⟩ :=
          hdec ⟨j.val - 1, by omega⟩ j (Fin.le_def.mpr (show j.val - 1 ≤ j.val by omega))
        exact_mod_cast this
  · -- `0 ≤ M j.succ − T j`
    rw [sub_nonneg]
    exact_mod_cast le_trans (hbound j) (admBound_le_Msucc M j)

/-- Running prefix-minimum `min(M⁰,…,M^{j+1})` (over indices `i ≤ j.succ`): the witness that
realises `Mval = 0` at a zero reduced width. -/
def runMin (M : Fin (L + 1) → ℕ) (j : Fin L) : ℕ :=
  (Finset.Iic j.succ).inf' ⟨j.succ, Finset.mem_Iic.mpr le_rfl⟩ M

/-- `runMin M j ≤ M i` for every `i ≤ j.succ`. -/
theorem runMin_le (M : Fin (L + 1) → ℕ) (j : Fin L) {i : Fin (L + 1)} (hi : i ≤ j.succ) :
    runMin M j ≤ M i :=
  Finset.inf'_le M (Finset.mem_Iic.mpr hi)

/-- `runMin` is antitone in the index: a longer prefix has a smaller minimum. -/
theorem runMin_anti (M : Fin (L + 1) → ℕ) {i j : Fin L} (hij : i ≤ j) :
    runMin M j ≤ runMin M i := by
  unfold runMin
  apply Finset.le_inf'
  intro x hx
  rw [Finset.mem_Iic] at hx
  refine Finset.inf'_le M (Finset.mem_Iic.mpr (le_trans hx ?_))
  rw [Fin.le_def, Fin.val_succ, Fin.val_succ]; have := Fin.le_def.mp hij; omega

/-- `runMin M j ≤ admBound M j`: at `j = 0`, `runMin ≤ M 0` and `runMin ≤ M 1` give
`runMin ≤ min(M⁰,M¹)`; else `admBound = M^{j+1}` and `runMin ≤ M^{j+1}`. -/
theorem runMin_le_admBound (M : Fin (L + 1) → ℕ) (j : Fin L) : runMin M j ≤ admBound M j := by
  unfold admBound
  split
  · next h =>
      apply le_min
      · exact runMin_le M j (Fin.zero_le _)
      · rw [← succ_eq_one_of_val_zero j h]; exact runMin_le M j le_rfl
  · next h => exact runMin_le M j le_rfl

/-- The witness `runMin` is admissible whenever some reduced width is `0`. -/
theorem runMin_mem_Adm (M : Fin (L + 1) → ℕ) (hz : ∃ s, M s = 0) : runMin M ∈ Adm M := by
  rw [Adm, mem_filter]
  refine ⟨?_, fun j => runMin_le_admBound M j, fun i j hij => runMin_anti M hij, ?_⟩
  · rw [Fintype.mem_piFinset]; intro j; rw [mem_range]
    exact Nat.lt_succ_of_le (runMin_le_admBound M j)
  · -- last is 0 (uses the zero width)
    intro j hj
    obtain ⟨s, hs⟩ := hz
    have : runMin M j ≤ M s := runMin_le M j (by rw [Fin.le_def, Fin.val_succ]; omega)
    omega

/-- `Mval` at the running-min witness is `0`: each summand vanishes because
`runMin M j = min (tPrev) (M^{j+1})`, so one factor is zero. -/
theorem Mval_runMin_eq_zero (M : Fin (L + 1) → ℕ) (hz : ∃ s, M s = 0) :
    Mval M (runMin M) = 0 := by
  unfold Mval
  apply Finset.sum_eq_zero
  intro j _
  -- `tPrev M (runMin M) j = ↑p` for the `ℕ` value `p`, and `runMin M j = min p (M j.succ)`
  set p : ℕ := if j.val = 0 then M 0 else runMin M ⟨j.val - 1, by omega⟩ with hp
  have htp : tPrev M (runMin M) j = (p : ℤ) := by
    unfold tPrev; rw [hp]; split <;> rfl
  have hmin : runMin M j = min p (M j.succ) := by
    apply le_antisymm
    · apply le_min
      · rw [hp]; split
        · next h => exact runMin_le M j (Fin.zero_le _)
        · next h =>
            exact runMin_anti M (Fin.le_def.mpr (show j.val - 1 ≤ j.val by omega))
      · exact runMin_le M j le_rfl
    · apply Finset.le_inf'
      intro i hi
      rw [Finset.mem_Iic, Fin.le_def, Fin.val_succ] at hi
      rcases Nat.lt_or_ge i.val (j.val + 1) with hlt | hge
      · -- `i ≤ ⟨j-1⟩.succ`, so `p ≤ M i`
        refine le_trans (min_le_left _ _) ?_
        rw [hp]; split
        · next h =>
            have : i = (0 : Fin (L + 1)) := Fin.ext (by rw [Fin.val_zero]; omega)
            rw [this]
        · next h =>
            apply runMin_le M ⟨j.val - 1, by omega⟩
            exact Fin.le_def.mpr (show i.val ≤ (j.val - 1) + 1 by omega)
      · -- `i = j.succ`
        have : i = j.succ := Fin.ext (by rw [Fin.val_succ]; omega)
        rw [this]; exact min_le_right _ _
  rw [htp, hmin]
  rcases le_total p (M j.succ) with hle | hge
  · rw [min_eq_left hle]; simp
  · rw [min_eq_right hge]; simp

/-- **Zero reduced width ⟹ the singular core vanishes**: if some reduced width `M s = 0` then
`lambdaCore M = 0` (worked.tex:710-711; brute-force verified). -/
theorem lambdaCore_eq_zero_of_exists_width_zero (M : Fin (L + 1) → ℕ) (hz : ∃ s, M s = 0) :
    lambdaCore M = 0 := by
  have hmin : (Adm M).inf' (Adm_nonempty M) (Mval M) = 0 := by
    apply le_antisymm
    · calc (Adm M).inf' (Adm_nonempty M) (Mval M)
          ≤ Mval M (runMin M) := Finset.inf'_le _ (runMin_mem_Adm M hz)
        _ = 0 := Mval_runMin_eq_zero M hz
    · exact Finset.le_inf' _ _ (fun T hT => Mval_nonneg_of_mem_Adm M T hT)
  unfold lambdaCore; rw [hmin]; simp

/-- **`aoyagiLambda` at a zero reduced width**: if `H s ≤ r` for some `s` (a layer at rank `≤ r`,
so `M^{(s)} = H^{(s)} − r = 0`) then `aoyagiLambda` degenerates to the regular Morse block alone
(the singular core drops). -/
theorem aoyagiLambda_of_exists_width_le (H : Fin (L + 1) → ℕ) (r : ℕ) (h : ∃ s, H s ≤ r) :
    aoyagiLambda H r = (-(r : ℚ) ^ 2 + r * (H 0 + H (Fin.last L))) / 2 := by
  unfold aoyagiLambda
  obtain ⟨s, hs⟩ := h
  rw [lambdaCore_eq_zero_of_exists_width_zero _ ⟨s, Nat.sub_eq_zero_of_le hs⟩, add_zero]

end DLNFibre.DLN.RLCT
