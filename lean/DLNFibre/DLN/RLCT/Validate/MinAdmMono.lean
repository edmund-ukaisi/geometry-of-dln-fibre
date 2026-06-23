import DLNFibre.DLN.RLCT.Validate.RouteMNReg
import DLNFibre.DLN.RLCT.Validate.ResolutionAtlas

/-!
# `DLNFibre.DLN.RLCT.Validate.MinAdmMono` — componentwise monotonicity of the minimal codim (#149)

The binding-arithmetic monotonicity `minAdm (schurStateRed M) ≤ minAdm M` (`hMono`, the named hyp of
`BindingArith.bind_hnReg` — `0 ≤ bindNReg M`). pp-rstar's cert
(`r1-realizability-witness-codex/hmono-minadm-monotone-CERT.md`) adjudicated it TRUE and pinned the proof:
the genuine theorem is the **componentwise monotonicity** of the minimal codim `inf' Mval`,

    `(∀ i, M' i ≤ M i) → (Adm M').inf' _ (Mval M') ≤ (Adm M).inf' _ (Mval M)`,

of which `hMono` is the two-front-coordinate-drop corollary at `M' = schurStateRed M`. The load-bearing
object is the **running-min-cap transfer** `Adm M → Adm M'`,

    `T'_j := min_{k ≤ j}( min (T_k) (admBound M' k) )`

(the forward running minimum of the bound-capped exponent). The naive pointwise clamp FAILS (breaks
weak-decrease, 40/336); the running-min repairs it. The transfer lands in `Adm M'` (admissible) and drops
the value (`Mval M' (transfer T) ≤ Mval M T`), so `inf' (Mval M') ≤ Mval M' (transfer T*) ≤ Mval M T* =
inf' (Mval M)`.

**Trap pinned in the cert (do NOT prove a free per-term lemma):** the per-term drop
`(ρ'−T')(W'−T') ≤ (ρ−T)(W−T)` is FALSE as a standalone integer inequality (1678 counterexamples); it holds
on the transfer's image ONLY because every running-min cut coincides with a local width/ρ drop (Case B).
The Mval-drop must thread the running-min structure, not a context-free per-term lemma.
-/

open scoped BigOperators
open Finset

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The clean per-term drop (the elementary integer lemma).** With the local cap `t' = min t (min a b)`,
and `a ≤ ρ`, `b ≤ w`, `t ≤ ρ`, `t ≤ w` (all `ℤ`), the product of the gaps drops:
`(a − t')(b − t') ≤ (ρ − t)(w − t)`. The per-`Mval`-term bound on the transfer image (verified 0/2M); the
FALSE "free" version (`t'` only `≤` the factors, not `= min`) is the cert trap. Proof: case on the min —
if `t' = t` both factors drop (`a−t ≤ ρ−t`, `b−t ≤ w−t`, nonneg); if `t' = a` or `t' = b` a factor is `0`
so `LHS = 0 ≤ RHS` (RHS `≥ 0`). -/
theorem perterm_drop {ρ w t a b : ℤ} (ha : a ≤ ρ) (hb : b ≤ w) (hta : t ≤ ρ) (htw : t ≤ w) :
    (a - min t (min a b)) * (b - min t (min a b)) ≤ (ρ - t) * (w - t) := by
  rcases le_total t (min a b) with hmin | hmin
  · -- `t ≤ min a b`, so `min t (min a b) = t`; both gaps drop.
    rw [min_eq_left hmin]
    have hab : t ≤ a ∧ t ≤ b := ⟨le_trans hmin (min_le_left _ _), le_trans hmin (min_le_right _ _)⟩
    have h1 : a - t ≤ ρ - t := by linarith
    have h2 : b - t ≤ w - t := by linarith
    exact mul_le_mul h1 h2 (by linarith [hab.2]) (by linarith)
  · -- `min a b ≤ t`, so `min t (min a b) = min a b`; one factor (the achieving min) is `0`.
    rw [min_eq_right hmin]
    have hrhs : 0 ≤ (ρ - t) * (w - t) := mul_nonneg (by linarith) (by linarith)
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, sub_self, zero_mul]; exact hrhs
    · rw [min_eq_right hab, sub_self, mul_zero]; exact hrhs

/-- The bound-capped exponent at index `j`: `min (T j) (admBound M' j)`. The running-min transfer takes the
forward minimum of this. -/
def capExp (M' : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) : ℕ :=
  min (T j) (admBound M' j)

/-- The running-min-cap transfer `T ↦ T'`, `T'_j := min_{k ≤ j} capExp M' T k` (forward running minimum of
the capped exponent). The map `Adm M → Adm M'` of the cert. Defined via `Finset.inf'` over the nonempty
`{k | k ≤ j}` (which contains `j`). -/
noncomputable def runMinCap (M' : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) : ℕ :=
  (Finset.Iic j).inf' ⟨j, Finset.mem_Iic.mpr le_rfl⟩ (capExp M' T)

/-- `runMinCap` is `≤` the capped exponent at the same index (the running min is below its last term). -/
theorem runMinCap_le_capExp (M' : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) :
    runMinCap M' T j ≤ capExp M' T j :=
  Finset.inf'_le _ (Finset.mem_Iic.mpr le_rfl)

/-- `runMinCap` is `≤` the original exponent (via the cap). -/
theorem runMinCap_le (M' : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) :
    runMinCap M' T j ≤ T j :=
  le_trans (runMinCap_le_capExp M' T j) (min_le_left _ _)

/-- `runMinCap` is weakly decreasing: `i ≤ j → runMinCap … j ≤ runMinCap … i` (the running min over a
larger down-set is smaller). -/
theorem runMinCap_antitone (M' : Fin (L + 1) → ℕ) (T : Fin L → ℕ) {i j : Fin L} (hij : i ≤ j) :
    runMinCap M' T j ≤ runMinCap M' T i := by
  rw [runMinCap, runMinCap, Finset.le_inf'_iff]
  intro b hb
  exact Finset.inf'_le _ (Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hb) hij))

/-- **Obligation 1 — `runMinCap` lands in `Adm M'`** (for `M' ≤ M` componentwise, `T ∈ Adm M`). The three
admissibility clauses: (a) `≤ admBound M'` (via the cap), (b) weak-decrease (running-min, `runMinCap_antitone`),
(c) last index `= 0` (cap ≤ `T (L-1) = 0`). -/
theorem runMinCap_mem_Adm (M M' : Fin (L + 1) → ℕ) (_hle : ∀ i, M' i ≤ M i)
    (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    runMinCap M' T ∈ Adm M' := by
  -- (a) the cap bound `runMinCap … j ≤ admBound M' j` (also the piFinset membership). Admissibility for
  -- `M'` rides only on the cap (`≤ admBound M'`), not on `M' ≤ M`; the value drop (Obl 2) uses `M' ≤ M`.
  have hbound : ∀ j : Fin L, runMinCap M' T j ≤ admBound M' j := fun j =>
    le_trans (runMinCap_le_capExp M' T j) (min_le_right _ _)
  -- clause (c): `T (L-1) = 0` from `hT`, and `runMinCap ≤ T`.
  rw [Adm, Finset.mem_filter] at hT ⊢
  obtain ⟨_, _, _, hlast⟩ := hT
  refine ⟨?_, hbound, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]; intro j; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (hbound j)
  · intro i j hij; exact runMinCap_antitone M' T hij
  · intro j hj; exact Nat.le_zero.mp (le_trans (runMinCap_le M' T j) (le_of_eq (hlast j hj)))

/-- `runMinCap … j ≤ tPrev M' (runMinCap …) j` (the predecessor exponent): for `j = 0` it is
`M' 0 ≥ admBound M' 0 ≥ runMinCap 0`; for `j ≥ 1` it is `runMinCap (j−1) ≥ runMinCap j` (antitone). The
`ℤ`-cast form, used in the per-term factor. -/
theorem runMinCap_le_tPrev (M' : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) :
    (runMinCap M' T j : ℤ) ≤ tPrev M' (runMinCap M' T) j := by
  unfold tPrev
  split
  · rename_i h0
    -- `runMinCap 0 ≤ admBound M' 0 = min (M' 0) (M' 1) ≤ M' 0`.
    have : runMinCap M' T j ≤ M' 0 := by
      refine le_trans (le_trans (runMinCap_le_capExp M' T j) (min_le_right _ _)) ?_
      unfold admBound; rw [if_pos h0]; exact min_le_left _ _
    exact_mod_cast this
  · rename_i h0
    -- `j ≥ 1`: `tPrev = runMinCap (j-1)` and `runMinCap j ≤ runMinCap (j-1)` (antitone, `j-1 ≤ j`).
    have hle' : runMinCap M' T j ≤ runMinCap M' T ⟨j.val - 1, by omega⟩ :=
      runMinCap_antitone M' T (by simp only [Fin.le_def]; omega)
    exact_mod_cast hle'

/-- `runMinCap … j ≤ M' j.succ` (the `W'` factor bound): for `j ≥ 1`, `admBound M' j = M' j.succ`; for
`j = 0`, `admBound M' 0 = min (M' 0) (M' 1) ≤ M' 1 = M' (0.succ)`. The `ℤ`-cast form. -/
theorem runMinCap_le_Msucc (M' : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) :
    (runMinCap M' T j : ℤ) ≤ (M' j.succ : ℤ) := by
  have : runMinCap M' T j ≤ M' j.succ := by
    refine le_trans (le_trans (runMinCap_le_capExp M' T j) (min_le_right _ _)) ?_
    unfold admBound
    split
    · rename_i h0
      have hsucc : j.succ = (1 : Fin (L + 1)) := by
        apply Fin.ext; rw [Fin.val_succ, h0, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [hsucc]; exact min_le_right _ _
    · exact le_refl _
  exact_mod_cast this

/-- **The characterization** `runMinCap … j = min (T j) (min (tPrev M' (runMinCap …) j) (M' j.succ))` (the
local cap, `ℤ`-cast). This is the load-bearing structural fact (verified 0-fail): `T'` equals the local min
of the original exponent, the running predecessor, and the width — NOT merely `≤` them (the cert trap). -/
theorem runMinCap_eq_local (M' : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) :
    (runMinCap M' T j : ℤ)
      = min (T j : ℤ) (min (tPrev M' (runMinCap M' T) j) (M' j.succ : ℤ)) := by
  apply le_antisymm
  · -- `≤`: `runMinCap j` is below each of the three.
    refine le_min ?_ (le_min (runMinCap_le_tPrev M' T j) (runMinCap_le_Msucc M' T j))
    exact_mod_cast runMinCap_le M' T j
  · -- `≥`: push the `ℕ→ℤ` cast inside the `inf'` (`comp_inf'_eq_inf'_comp`, `Nat.cast_min`), then
    -- `le_inf'`: for each `k ≤ j`, the min is below `↑(capExp k)`.
    rw [runMinCap,
      Finset.comp_inf'_eq_inf'_comp ⟨j, Finset.mem_Iic.mpr le_rfl⟩ (Nat.cast : ℕ → ℤ)
        (fun x y => Nat.cast_min x y)]
    apply Finset.le_inf'
    intro k hk
    have hkj : k ≤ j := Finset.mem_Iic.mp hk
    rcases eq_or_lt_of_le hkj with hkj' | hkj'
    · -- `k = j`: the min is below `↑(capExp j) = min ↑(T j) ↑(admBound M' j)`.
      rw [hkj']
      simp only [Function.comp_apply, capExp, Nat.cast_min]
      refine le_min (min_le_left _ _) ?_
      unfold admBound
      split
      · rename_i h0
        -- `j.succ = 1`, and `tPrev' j = M' 0` (since `j.val = 0`); so the middle factor IS `min (M'0) (M'1)`.
        have hsucc : j.succ = (1 : Fin (L + 1)) := by
          apply Fin.ext; rw [Fin.val_succ, h0, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
        have htp0 : tPrev M' (runMinCap M' T) j = (M' 0 : ℤ) := by unfold tPrev; rw [if_pos h0]
        refine le_trans (min_le_right _ _) ?_
        rw [htp0, hsucc]; push_cast; rfl
      · exact le_trans (min_le_right _ _) (min_le_right _ _)
    · -- `k < j`: `min(…) ≤ tPrev_j = ↑(runMinCap (j-1)) ≤ ↑(capExp k)` (since `k ≤ j-1`, `inf'_le`).
      have hj0 : j.val ≠ 0 := by omega
      have htp : tPrev M' (runMinCap M' T) j = (runMinCap M' T ⟨j.val - 1, by omega⟩ : ℤ) := by
        unfold tPrev; rw [if_neg hj0]
      have hk_le : k ≤ (⟨j.val - 1, by omega⟩ : Fin L) := by simp only [Fin.le_def]; omega
      have hrun : (runMinCap M' T ⟨j.val - 1, by omega⟩ : ℕ) ≤ capExp M' T k :=
        Finset.inf'_le _ (Finset.mem_Iic.mpr hk_le)
      simp only [Function.comp_apply]
      refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) ?_)
      rw [htp]; exact_mod_cast hrun

/-- `T j ≤ t⁽ʲ⁻¹⁾` on the admissible cone (weak-decrease + first-block bound). Local copy of the `private`
`ResolutionAtlas.Tle_tPrev`. -/
theorem T_le_tPrev (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    (T j : ℤ) ≤ tPrev M T j := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨hbound, hdec, _⟩ := hT.2
  unfold tPrev
  split
  · rename_i h0
    have hb : T j ≤ admBound M j := hbound j
    rw [admBound, if_pos h0] at hb
    exact_mod_cast le_trans hb (min_le_left _ _)
  · have hle : (⟨j.val - 1, by omega⟩ : Fin L) ≤ j := by simp only [Fin.le_def]; omega
    exact_mod_cast hdec _ _ hle

/-- `T j ≤ M⁽ʲ⁺¹⁾` on the admissible cone (the block bound). Local copy of the `private`
`ResolutionAtlas.Tle_Msucc`. -/
theorem T_le_Msucc (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    (T j : ℤ) ≤ (M j.succ : ℤ) := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨hbound, _, _⟩ := hT.2
  have hb : T j ≤ admBound M j := hbound j
  unfold admBound at hb
  split at hb
  · rename_i h0
    have hle : T j ≤ M 1 := le_trans hb (min_le_right _ _)
    have hsucc : j.succ = (1 : Fin (L + 1)) := by
      apply Fin.ext; rw [Fin.val_succ, h0, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [hsucc]; exact_mod_cast hle
  · exact_mod_cast hb

/-- **Obligation 2 — `runMinCap` drops the value** `Mval M' (runMinCap M' T) ≤ Mval M T` (for `M' ≤ M`,
`T ∈ Adm M`). Per-term via `perterm_drop` + the characterization `runMinCap_eq_local`: each summand
`(tPrev' − T')(M' − T')` is `≤ (tPrev − T)(M − T)` with `T' = min (T) (min tPrev' M')`, `tPrev' ≤ tPrev`
(predecessor antitone + `M' ≤ M`), `M' j.succ ≤ M j.succ`, `T ≤ tPrev`, `T ≤ M j.succ` (`T ∈ Adm M`). -/
theorem Mval_runMinCap_le (M M' : Fin (L + 1) → ℕ) (hle : ∀ i, M' i ≤ M i)
    (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    Mval M' (runMinCap M' T) ≤ Mval M T := by
  unfold Mval
  apply Finset.sum_le_sum
  intro j _
  -- per-term: set `t' := runMinCap M' T j`, characterised as `min (T j) (min tPrev' M' j.succ)`.
  have hchar := runMinCap_eq_local M' T j
  -- the three comparison facts (all ℤ):
  -- (1) `tPrev M' (runMinCap) j ≤ tPrev M T j` :  predecessor exponent drops (antitone + M'≤M)
  have ha : tPrev M' (runMinCap M' T) j ≤ tPrev M T j := by
    unfold tPrev
    split
    · rename_i h0; exact_mod_cast hle 0
    · rename_i h0; exact_mod_cast runMinCap_le M' T _
  -- (2) `M' j.succ ≤ M j.succ`
  have hb : (M' j.succ : ℤ) ≤ (M j.succ : ℤ) := by exact_mod_cast hle j.succ
  -- (3) `T j ≤ tPrev M T j`  and  (4) `T j ≤ M j.succ`  (from `T ∈ Adm M`)
  have hta : (T j : ℤ) ≤ tPrev M T j := T_le_tPrev M T hT j
  have htw : (T j : ℤ) ≤ (M j.succ : ℤ) := T_le_Msucc M T hT j
  -- assemble: the per-term drop with `a := tPrev'`, `b := M' j.succ`, `ρ := tPrev M T`, `w := M j.succ`,
  -- `t := T j`, `t' = min t (min a b) = runMinCap j` (by `hchar`).
  rw [hchar]
  exact perterm_drop ha hb hta htw

/-- **The componentwise monotonicity of the minimal codim.** `M' ≤ M` componentwise ⟹
`inf' (Mval M') ≤ inf' (Mval M)`. The chain: take the achiever `T*` of `inf' (Mval M)`; its transfer
`runMinCap M' T*` is in `Adm M'` (Obl 1), so `inf' (Mval M') ≤ Mval M' (runMinCap M' T*)` (`inf'_le`),
and `Mval M' (runMinCap M' T*) ≤ Mval M T* = inf' (Mval M)` (Obl 2 + achiever). -/
theorem inf'_Mval_mono (M M' : Fin (L + 1) → ℕ) (hle : ∀ i, M' i ≤ M i) :
    (Adm M').inf' (Adm_nonempty M') (Mval M') ≤ (Adm M).inf' (Adm_nonempty M) (Mval M) := by
  obtain ⟨Tstar, hTstar_mem, hTstar_eq⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
  calc (Adm M').inf' (Adm_nonempty M') (Mval M')
      ≤ Mval M' (runMinCap M' Tstar) :=
        Finset.inf'_le _ (runMinCap_mem_Adm M M' hle Tstar hTstar_mem)
    _ ≤ Mval M Tstar := Mval_runMinCap_le M M' hle Tstar hTstar_mem
    _ = (Adm M).inf' (Adm_nonempty M) (Mval M) := hTstar_eq.symm

/-- `schurStateRed M ≤ M` componentwise (drops the two front pivot widths by 1). -/
theorem schurStateRed_le (M : Fin (L + 1) → ℕ) (i : Fin (L + 1)) : schurStateRed M i ≤ M i := by
  unfold schurStateRed
  split <;> omega

/-- **`hMono` — `lambdaCore (schurStateRed M) ≤ lambdaCore M`** (the binding-arithmetic monotonicity, #149).
The corollary of `inf'_Mval_mono` at `M' = schurStateRed M` (componentwise `≤ M`). -/
theorem lambdaCore_schurStateRed_le (M : Fin (L + 1) → ℕ) :
    lambdaCore (schurStateRed M) ≤ lambdaCore M := by
  unfold lambdaCore
  have h := inf'_Mval_mono M (schurStateRed M) (schurStateRed_le M)
  have hq : ((((Adm (schurStateRed M)).inf' (Adm_nonempty (schurStateRed M))
        (Mval (schurStateRed M))) : ℤ) : ℚ)
      ≤ ((((Adm M).inf' (Adm_nonempty M) (Mval M)) : ℤ) : ℚ) := by exact_mod_cast h
  linarith

/-- **The `degenChild`-consistency corollary** `isLeafNode M → isLeafNode (schurStateRed M)` (child-of-leaf
is a leaf). The `binding_recursion_of_step` apply takes `degenChild := isLeafNode ∘ schurStateRed`; this is
the base-case consistency that a leaf parent has a leaf reduced child. A corollary of `inf'_Mval_mono`:
`inf'(Mval(schurStateRed M)) ≤ inf'(Mval M)`, and both `inf'` are `≥ 0` (`Mval ≥ 0` on `Adm`), so
`(inf' M).toNat = 0 ⟹ inf' M ≤ 0 ⟹ inf'(schurStateRed M) ≤ 0 ⟹ (inf'(schurStateRed M)).toNat = 0`. -/
theorem isLeafNode_schurStateRed_of_isLeafNode (M : Fin (L + 1) → ℕ) (hleaf : isLeafNode M) :
    isLeafNode (schurStateRed M) := by
  unfold isLeafNode at hleaf ⊢
  -- `inf' M ≤ 0` from `(inf' M).toNat = 0` (the inf' is `≥ 0`, so `.toNat = 0 ⟺ inf' ≤ 0`).
  have hMle : (Adm M).inf' (Adm_nonempty M) (Mval M) ≤ 0 := Int.toNat_eq_zero.mp hleaf
  -- monotonicity + the bound give `inf'(schurStateRed M) ≤ 0`.
  have hmono := inf'_Mval_mono M (schurStateRed M) (schurStateRed_le M)
  have hredle : (Adm (schurStateRed M)).inf' (Adm_nonempty (schurStateRed M))
      (Mval (schurStateRed M)) ≤ 0 := le_trans hmono hMle
  exact Int.toNat_eq_zero.mpr hredle

end DLNFibre.DLN.RLCT
