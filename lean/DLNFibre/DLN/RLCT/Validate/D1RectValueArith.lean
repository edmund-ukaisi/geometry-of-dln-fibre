import DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2Build

/-!
# `DLNFibre.DLN.RLCT.Validate.D1RectValueArith` — the RECTANGULAR value arithmetic (item 2)

The banked §6 value inequality `lambdaCore(square m) ≤ extra/2 + lambdaCore(M')` is SQUARE-only
(single reduced width `m`, `extra = m(a+b) − ab`). The general-`H` deepest reduced widths at L = 2
are RECTANGULAR: `M = (m0, m1, m2) = (H0−r, H1−r, H2−r)`. This module supplies the rectangular
generalisation — the `hDom` value comparison at a general `H`.

## The RIGHT `extra` is CROSS-paired (decorrelated: two pen-and-paper seats + Codex xhigh)

The value inequality holds UNCONDITIONALLY iff `extra = a·m2 + b·m0 − ab` — the front-layer rank
rise `a` weighted by the BACK reduced width `m2`, the back rise `b` by the FRONT width `m0` (`ab`
correction). The straight-paired `a·m0 + b·m2 − ab` FAILS off `m0 = m2` (a realizable family). The
DLN Jacobian excess is exactly this cross-paired form (`rank D = (r+b)H0 + (r+a)H2 − (r+a)(r+b)`,
H1-independent, incl-excl on the column/row spans), so the geometry and the value agree — the headline
step `rlct ≤ extra/2 + core` closes with NO sign condition. The square specialisation `m0 = m2 = m`
recovers `m(a+b) − ab`.

## The mechanism (the rectangular telescope)

The exact ℤ identity (mirroring the banked `Mval_Mprime_add_extra_eq_square`):

    (a·M2 + b·M0 − ab) + Mval(M', ![t0, 0]) = Mval(M, ![t0+a, 0]),   M' = (M0−a, M1−a−b, M2−b),

with the UNIQUE shift `s = a`. The `M'`-minimiser `T*` (Adm-last `T* 1 = 0`) maps under this identity
to an admissible square-`M` exponent `![T* 0 + a, 0]` (Adm-lift: `T* 0 + a ≤ min(M0, M1)`
unconditionally from `a ≤ M0`, `a+b ≤ M1`), dominating the `M`-infimum. Requires the honest-subtraction
constraints `a ≤ M0`, `a + b ≤ M1`, `b ≤ M2`.

Scope L = 2 (`M : Fin 3 → ℕ`). Pure `Mval`/`Adm`/`Finset.inf'` algebra; no analysis.
-/

open scoped ENNReal
namespace DLNFibre.DLN.RLCT

/-- The RECTANGULAR `extra` (the cross-paired Morse-square count): `a·M2 + b·M0 − ab`. The front-rank
rise `a` weighted by the back reduced width `M2`, the back rise `b` by the front `M0`. Reduces to the
square `extraCount m a b = m(a+b) − ab` when `M0 = M2 = m`. -/
def extraCountRect (M0 M2 a b : ℕ) : ℕ := a * M2 + b * M0 - a * b

/-- The rectangular degraded reduced widths `M' = (M0−a, M1−a−b, M2−b) : Fin 3 → ℕ` at a general `M`. -/
def MprimeRect (M : Fin 3 → ℕ) (a b : ℕ) : Fin 3 → ℕ := ![M 0 - a, M 1 - a - b, M 2 - b]

/-- **The rectangular telescope identity** `extra + Mval(M', T) = Mval(M, ![T 0 + a, 0])` over ℤ,
under the honest-subtraction constraints `a ≤ M0`, `a + b ≤ M1`, `b ≤ M2` and `T 1 = 0`. The unique
shift is `s = a`. Generalises `Mval_Mprime_add_extra_eq_square` (which is the `M0 = M1 = M2` case). -/
theorem Mval_MprimeRect_add_extra_eq (M : Fin 3 → ℕ) (a b : ℕ) (T : Fin 2 → ℕ)
    (ha : a ≤ M 0) (hab : a + b ≤ M 1) (hb : b ≤ M 2) (hT1 : T 1 = 0) :
    (extraCountRect (M 0) (M 2) a b : ℤ) + Mval (MprimeRect M a b) T
      = Mval M ![T 0 + a, 0] := by
  -- honest casts (all subtractions nonneg)
  have hcast_0a : ((M 0 - a : ℕ) : ℤ) = (M 0 : ℤ) - a := by omega
  have hcast_1ab : ((M 1 - a - b : ℕ) : ℤ) = (M 1 : ℤ) - a - b := by omega
  have hcast_2b : ((M 2 - b : ℕ) : ℤ) = (M 2 : ℤ) - b := by omega
  have hab_le : a * b ≤ a * (M 2) + b * (M 0) := by nlinarith [ha, hb, Nat.zero_le a, Nat.zero_le b]
  have hcast_extra : (extraCountRect (M 0) (M 2) a b : ℤ) = (a : ℤ) * (M 2) + b * (M 0) - a * b := by
    rw [extraCountRect, Nat.cast_sub hab_le]; push_cast; ring
  -- expand both sides via `Mval_L2`
  rw [Mval_L2, Mval_L2]
  -- read off the width / exponent entries
  have hM0 : (MprimeRect M a b) 0 = M 0 - a := rfl
  have hM1 : (MprimeRect M a b) 1 = M 1 - a - b := rfl
  have hM2 : (MprimeRect M a b) 2 = M 2 - b := rfl
  have hc0 : (![T 0 + a, 0] : Fin 2 → ℕ) 0 = T 0 + a := rfl
  have hc1 : (![T 0 + a, 0] : Fin 2 → ℕ) 1 = 0 := rfl
  rw [hM0, hM1, hM2, hc0, hc1, hT1]
  push_cast [hcast_0a, hcast_1ab, hcast_2b, hcast_extra]
  ring

/-- **The Adm-lift** `T ∈ Adm(M') ⟹ ![T 0 + a, 0] ∈ Adm(M)` (rectangular). The binding clause is the
block bound `T 0 + a ≤ admBound M 0 = min(M0, M1)`, unconditional from `a ≤ M0` and `a + b ≤ M1`
(via `admBound(M') 0 = min(M0−a, M1−a−b)` ⟹ `T 0 ≤ min(M0−a, M1−a−b)` ⟹ `T 0 + a ≤ min(M0, M1)`). -/
theorem cand_mem_Adm_rect (M : Fin 3 → ℕ) (a b : ℕ) (ha : a ≤ M 0) (hab : a + b ≤ M 1)
    {T : Fin 2 → ℕ} (hT : T ∈ Adm (MprimeRect M a b)) :
    (![T 0 + a, 0] : Fin 2 → ℕ) ∈ Adm M := by
  -- from `hT`, the first-coord block bound on `T`
  rw [Adm, Finset.mem_filter] at hT
  have hbd := hT.2.1 0
  have hbd' : T 0 ≤ min (M 0 - a) (M 1 - a - b) := by
    rw [admBound, Fin.val_zero, if_pos rfl] at hbd
    simpa only [MprimeRect, Matrix.cons_val_zero, Matrix.cons_val_one] using hbd
  have hTshift : T 0 + a ≤ min (M 0) (M 1) := by omega
  -- assemble membership for the candidate
  have hc0 : (![T 0 + a, 0] : Fin 2 → ℕ) 0 = T 0 + a := rfl
  have hc1 : (![T 0 + a, 0] : Fin 2 → ℕ) 1 = 0 := rfl
  have hb0 : admBound M 0 = min (M 0) (M 1) := by rw [admBound]; simp
  have hb1 : admBound M 1 = M (Fin.succ 1) := by rw [admBound]; norm_num
  have hbound : ∀ j : Fin 2, (![T 0 + a, 0] : Fin 2 → ℕ) j ≤ admBound M j := by
    rw [Fin.forall_fin_two, hc0, hc1, hb0]
    exact ⟨hTshift, Nat.zero_le _⟩
  rw [Adm, Finset.mem_filter]
  refine ⟨?_, hbound, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro j; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (hbound j)
  · -- weak-decrease: `T 1 = 0 ≤ T 0`
    intro i j hij
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · rw [Fin.le_zero_iff.1 hij]
    · have hj1 : j'.succ = (1 : Fin 2) := by
        have : j' = (0 : Fin 1) := Subsingleton.elim _ _
        rw [this]; rfl
      rw [hj1, hc1]; exact Nat.zero_le _
  · -- last-coordinate clause: `j.val = 1 → T j = 0`
    intro j hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · exact absurd hj (by simp only [Fin.val_zero]; omega)
    · have hj1 : j'.succ = (1 : Fin 2) := by
        have : j' = (0 : Fin 1) := Subsingleton.elim _ _
        rw [this]; rfl
      rw [hj1, hc1]

/-- **The rectangular value inequality** (item 2), over `ℚ`:

    lambdaCore(M) ≤ extraCountRect(M0, M2, a, b)/2 + lambdaCore(M'),   M' = (M0−a, M1−a−b, M2−b),

under `a ≤ M0`, `a + b ≤ M1`, `b ≤ M2`. The `M'`-minimiser `T*` maps under the telescope identity to
an admissible `M`-exponent dominating the `M`-infimum. Generalises `extra_half_add_lambdaCore_Mprime_ge_square`. -/
theorem lambdaCore_le_extraRect_half_add_lambdaCore_Mprime (M : Fin 3 → ℕ) (a b : ℕ)
    (ha : a ≤ M 0) (hab : a + b ≤ M 1) (hb : b ≤ M 2) :
    lambdaCore M
      ≤ (extraCountRect (M 0) (M 2) a b : ℚ) / 2 + lambdaCore (MprimeRect M a b) := by
  -- the `M'`-side infimum minimiser
  obtain ⟨T, hTmem, hTeq⟩ :=
    Finset.exists_mem_eq_inf' (Adm_nonempty (MprimeRect M a b)) (Mval (MprimeRect M a b))
  have hT1 : T 1 = 0 := Adm_L2_last_zero _ hTmem
  have hcand : (![T 0 + a, 0] : Fin 2 → ℕ) ∈ Adm M := cand_mem_Adm_rect M a b ha hab hTmem
  set Isq : ℤ := (Adm M).inf' (Adm_nonempty M) (Mval M) with hIsq
  set Ip : ℤ := (Adm (MprimeRect M a b)).inf' (Adm_nonempty (MprimeRect M a b))
    (Mval (MprimeRect M a b)) with hIp
  have hkey : Isq ≤ (extraCountRect (M 0) (M 2) a b : ℤ) + Ip := by
    rw [hTeq]
    calc Isq ≤ Mval M ![T 0 + a, 0] := Finset.inf'_le _ hcand
      _ = (extraCountRect (M 0) (M 2) a b : ℤ) + Mval (MprimeRect M a b) T :=
          (Mval_MprimeRect_add_extra_eq M a b T ha hab hb hT1).symm
  rw [lambdaCore, lambdaCore, ← hIsq, ← hIp]
  have hkeyQ : (Isq : ℚ) ≤ (extraCountRect (M 0) (M 2) a b : ℚ) + (Ip : ℚ) := by exact_mod_cast hkey
  linarith [hkeyQ]

/-- **The `ℝ≥0∞` form of the rectangular value inequality** (the shape the RLCT chain consumes):

    ofReal(lambdaCore M) ≤ (extraCountRect M0 M2 a b : ℝ≥0∞)/2 + ofReal(lambdaCore M').

Bridges the `ℚ` lemma through `ENNReal.ofReal` (both `lambdaCore`s nonneg via `lambdaCore_nonneg_L2`).
Generalises `coreDeepest_le_extra_half_add_lambdaCore_Mprime`. -/
theorem coreRect_le_extraRect_half_add_lambdaCore_Mprime (M : Fin 3 → ℕ) (a b : ℕ)
    (ha : a ≤ M 0) (hab : a + b ≤ M 1) (hb : b ≤ M 2) :
    ENNReal.ofReal (lambdaCore M : ℝ)
      ≤ (extraCountRect (M 0) (M 2) a b : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (MprimeRect M a b) : ℝ) := by
  have hQ := lambdaCore_le_extraRect_half_add_lambdaCore_Mprime M a b ha hab hb
  have hMnn : (0 : ℚ) ≤ lambdaCore M := lambdaCore_nonneg_L2 _
  have hpnn : (0 : ℚ) ≤ lambdaCore (MprimeRect M a b) := lambdaCore_nonneg_L2 _
  have hext2 : (0 : ℝ) ≤ (extraCountRect (M 0) (M 2) a b : ℝ) / 2 := by positivity
  have hof2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num
  have hbridge : (extraCountRect (M 0) (M 2) a b : ℝ≥0∞) / 2
      = ENNReal.ofReal ((extraCountRect (M 0) (M 2) a b : ℝ) / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_natCast, hof2]
  rw [hbridge, ← ENNReal.ofReal_add hext2 (by exact_mod_cast hpnn)]
  apply ENNReal.ofReal_le_ofReal
  have hQR : (lambdaCore M : ℝ)
      ≤ (extraCountRect (M 0) (M 2) a b : ℝ) / 2 + (lambdaCore (MprimeRect M a b) : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hQ
    push_cast at hcast
    linarith [hcast]
  linarith [hQR]

end DLNFibre.DLN.RLCT
