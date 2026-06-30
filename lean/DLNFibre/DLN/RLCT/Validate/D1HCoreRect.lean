import DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2Build

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HCoreRect` — the RECTANGULAR `hCore` arithmetic (L = 2)

This module ports the banked SQUARE `hCore` arithmetic
(`extra_half_add_lambdaCore_Mprime_ge_square`, `D1ChartProducerL2Build`:178) to the genuinely
RECTANGULAR deepest reduced widths `M : Fin 3 → ℕ` (`M = H − r`, possibly non-square). It is PURE
`ℚ`/`Mval`/`Adm` algebra — no R1, no analysis.

## What this module lands

The middle-stratum `hCore` at L = 2 needs the self-contained arithmetic

    lambdaCore M ≤ extra/2 + lambdaCore M',   extra = M0·b + M2·a − a·b,
    M' = (M0−a, M1−a−b, M2−b),

for the rectangular deepest widths `M` and the middle-stratum rank-drop `(a, b)`
(`a = rank(A₁)−r`, `b = rank(A₂)−r`), under the admissibility `a ≤ M0`, `a + b ≤ M1`, `b ≤ M2`
(the `ℕ`-subtractions in `M'` honest). The deepest reduced widths at L = 2 are `M` itself, so
`coreDeepest = lambdaCore M`.

⚠️ The CORRECT extra is `M0·b + M2·a − a·b` — the rank of `d·prod = {A₂X + YA₁}` (dim
`q·H0 + p·H2 − p·q`). At SQUARE widths (`M = (m,m,m)`) it coincides with the square engine's
`m(a+b) − ab` (`extraCount`), which is why the rectangular case is a genuinely separate port (the
square `extraCount` is WRONG at non-square widths).

## Proof key (the exact shift identity, design-pass verified)

The rectangular analog of the banked square shift `Mval_Mprime_add_extra_eq_square`
(`D1ChartProducerL2Build`:92):

    extra + Mval(M', (t, 0)) = Mval(M, (t+a, 0)).

Admissibility transports: `t ≤ min(M0−a, M1−a−b) ⟹ t + a ≤ min(M0, M1) = admBound M 0`, so the
`M'`-minimiser maps to an admissible `M`-exponent, dominating the `M`-infimum. Verified ZERO
violations across the sweep (`0 ≤ M0, M1, M2 ≤ 6`, all admissible `(a,b)`); anchor `M = (2,3,2)`
(`H = (3,4,3)`, `r = 1`): `lambdaCore = 2`, every realizable stratum exactly `2` (equality).

Scope L = 2 only (`M : Fin 3 → ℕ`). This module is a LEAF: it lands the arithmetic and the
`ℝ≥0∞`-cast form that the middle-stratum `D1PerVChartObligation.hCore`
(`RouteMD1ForallV`:95) consumes; it does NOT edit `D1ChartProducerL2Build` (single-writer) nor wire
the obligation.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-! ## §1 — the rectangular degraded widths + corrected extra -/

/-- The middle-stratum degraded RECTANGULAR reduced widths `M' = (M0−a, M1−a−b, M2−b) : Fin 3 → ℕ`,
for general deepest widths `M : Fin 3 → ℕ`. -/
def MprimeRect (M : Fin 3 → ℕ) (a b : ℕ) : Fin 3 → ℕ :=
  ![M 0 - a, M 1 - a - b, M 2 - b]

/-- The CORRECTED rectangular `extra` Morse-square count `M0·b + M2·a − a·b` (`= nReg_v − nReg`
at the middle stratum; the rank of `d·prod = {A₂X + YA₁}`). At square widths `M = (m,m,m)` it equals
the square engine's `extraCount m a b = m(a+b) − ab`. -/
def extraRect (M : Fin 3 → ℕ) (a b : ℕ) : ℕ := M 0 * b + M 2 * a - a * b

/-! ## §2 — the banked symbolic shift identity (rectangular) -/

/-- **The rectangular shift identity** `extra + Mval(M', T) = Mval(M, ![T 0 + a, 0])` (the
`extra + D_{a,b}(t) = F_M(a+t)` at `t = T 0`, `T 1 = 0`). Over `ℤ`, verified exact by the design
pass (sympy + the rectangular sweep). Requires `a ≤ M 0`, `a + b ≤ M 1`, `b ≤ M 2` (the
middle-stratum admissibility ensuring the `ℕ`-subtractions in `M'` are honest). The corrected
`extraRect` `M0·b + M2·a − a·b` is the unique count making this identity hold at rectangular
widths. -/
theorem Mval_MprimeRect_add_extra_eq (M : Fin 3 → ℕ) (a b : ℕ) (T : Fin 2 → ℕ)
    (ha : a ≤ M 0) (hab : a + b ≤ M 1) (hb : b ≤ M 2) (hT1 : T 1 = 0) :
    (extraRect M a b : ℤ) + Mval (MprimeRect M a b) T
      = Mval M ![T 0 + a, 0] := by
  -- honest casts (all subtractions nonneg)
  have hcast_0a : ((M 0 - a : ℕ) : ℤ) = (M 0 : ℤ) - a := by omega
  have hcast_1ab : ((M 1 - a - b : ℕ) : ℤ) = (M 1 : ℤ) - a - b := by omega
  have hcast_2b : ((M 2 - b : ℕ) : ℤ) = (M 2 : ℤ) - b := by omega
  -- the extra is honest: `a*b ≤ M0*b + M2*a` (since `a ≤ M0`, so `a*b ≤ M0*b`)
  have hab_le : a * b ≤ M 0 * b + M 2 * a := by nlinarith [Nat.mul_le_mul_right b ha]
  have hcast_extra : (extraRect M a b : ℤ) = (M 0 : ℤ) * b + (M 2 : ℤ) * a - a * b := by
    rw [extraRect, Nat.cast_sub hab_le]; push_cast; ring
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

/-! ## §3 — admissibility transport -/

/-- The candidate exponent `![t + a, 0]` lands in `Adm M` provided `t + a ≤ min (M 0) (M 1)`. The
binding clause is the block bound `t + a ≤ admBound M 0 = min (M 0) (M 1)`; weak-decrease and the
last-coordinate clause hold by `0 ≤ t + a` and `(![·,0]) 1 = 0`. (General `M`; the square version
`cand_mem_Adm_square` specialises this.) -/
theorem cand_mem_Adm_rect (M : Fin 3 → ℕ) (a t : ℕ) (htm : t + a ≤ min (M 0) (M 1)) :
    (![t + a, 0] : Fin 2 → ℕ) ∈ Adm M := by
  have hc0 : (![t + a, 0] : Fin 2 → ℕ) 0 = t + a := rfl
  have hc1 : (![t + a, 0] : Fin 2 → ℕ) 1 = 0 := rfl
  have hb0 : admBound M 0 = min (M 0) (M 1) := by rw [admBound]; simp
  have hb1 : admBound M 1 = M 2 := by rw [admBound]; simp [Fin.succ]
  -- per-index bound `T j ≤ admBound j`, via `Fin.forall_fin_two`
  have hbound : ∀ j : Fin 2, (![t + a, 0] : Fin 2 → ℕ) j ≤ admBound M j := by
    rw [Fin.forall_fin_two, hc0, hc1, hb0, hb1]; exact ⟨htm, Nat.zero_le _⟩
  rw [Adm, Finset.mem_filter]
  refine ⟨?_, hbound, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro j; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (hbound j)
  · -- weak-decrease `T j ≤ T i` for `i ≤ j`
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

/-- For `T ∈ Adm (M' = (M0−a, M1−a−b, M2−b))`, the first exponent transports: `T 0 + a ≤
min (M 0) (M 1)` (the block bound `admBound M' 0 = min (M0−a) (M1−a−b)`, plus `a ≤ M0`,
`a + b ≤ M1`). -/
theorem Adm_MprimeRect_first_bound (M : Fin 3 → ℕ) (a b : ℕ)
    (ha : a ≤ M 0) (hab : a + b ≤ M 1) {T : Fin 2 → ℕ}
    (hT : T ∈ Adm (MprimeRect M a b)) : T 0 + a ≤ min (M 0) (M 1) := by
  rw [Adm, Finset.mem_filter] at hT
  have hbd := hT.2.1 0
  have hbd' : T 0 ≤ min (M 0 - a) (M 1 - a - b) := by
    rw [admBound, Fin.val_zero, if_pos rfl] at hbd
    simpa only [MprimeRect, Matrix.cons_val_zero, Matrix.cons_val_one] using hbd
  -- `T 0 ≤ min (M0−a) (M1−a−b)`; with `a ≤ M0`, `a + b ≤ M1` gives `T 0 + a ≤ min (M0) (M1)`.
  omega

/-! ## §4 — the self-contained rectangular arithmetic lemma (pure `ℚ`) -/

/-- **§4 — the rectangular `hCore` arithmetic lemma.** `lambdaCore M ≤ extra/2 + lambdaCore M'` over
`ℚ`, for the rectangular deepest widths `M : Fin 3 → ℕ` and the middle-stratum data `a ≤ M0`,
`a + b ≤ M1`, `b ≤ M2`. The deepest reduced widths at L = 2 are `M`, so `coreDeepest =
lambdaCore M`. Pure `Mval`/`Adm`/`Finset.inf'` algebra: the `M'`-minimiser `T*` (Adm-last
`T* 1 = 0`) maps under the shift identity `Mval_MprimeRect_add_extra_eq` to an admissible
`M`-exponent `![T* 0 + a, 0]`,
dominating the `M`-infimum. A DIRECT PORT of the banked square
`extra_half_add_lambdaCore_Mprime_ge_square`. -/
theorem lambdaCore_le_extraRect_half_add_lambdaCore_MprimeRect (M : Fin 3 → ℕ) (a b : ℕ)
    (ha : a ≤ M 0) (hab : a + b ≤ M 1) (hb : b ≤ M 2) :
    lambdaCore M
      ≤ (extraRect M a b : ℚ) / 2 + lambdaCore (MprimeRect M a b) := by
  -- the `M'`-side infimum minimiser
  obtain ⟨T, hTmem, hTeq⟩ :=
    Finset.exists_mem_eq_inf' (Adm_nonempty (MprimeRect M a b)) (Mval (MprimeRect M a b))
  have hT1 : T 1 = 0 := Adm_L2_last_zero _ hTmem
  have hTbound : T 0 + a ≤ min (M 0) (M 1) := Adm_MprimeRect_first_bound M a b ha hab hTmem
  -- the dominating `M`-exponent
  have hcand : (![T 0 + a, 0] : Fin 2 → ℕ) ∈ Adm M :=
    cand_mem_Adm_rect M a (T 0) hTbound
  -- name the two `ℤ`-valued infima
  set IM : ℤ := (Adm M).inf' (Adm_nonempty M) (Mval M) with hIM
  set Ip : ℤ := (Adm (MprimeRect M a b)).inf' (Adm_nonempty (MprimeRect M a b))
    (Mval (MprimeRect M a b)) with hIp
  -- `inf'_M Mval(M) ≤ Mval(M, cand) = extra + Mval(M', T) = extra + inf'_{M'} Mval(M')`
  have hkey : IM ≤ (extraRect M a b : ℤ) + Ip := by
    rw [hTeq]
    calc IM ≤ Mval M ![T 0 + a, 0] := Finset.inf'_le _ hcand
      _ = (extraRect M a b : ℤ) + Mval (MprimeRect M a b) T :=
          (Mval_MprimeRect_add_extra_eq M a b T ha hab hb hT1).symm
  -- lift the `ℤ` inequality through `lambdaCore = (1/2)·(inf' Mval)`
  rw [lambdaCore, lambdaCore, ← hIM, ← hIp]
  have hkeyQ : (IM : ℚ) ≤ (extraRect M a b : ℚ) + (Ip : ℚ) := by exact_mod_cast hkey
  linarith [hkeyQ]

/-- `lambdaCore M ≥ 0` at L = 2 (admissible `Mval ≥ 0` on the cone ⟹ `inf' ≥ 0`). Reuses
`Mval_nonneg_of_adm`. (General `M`; mirrors `lambdaCore_nonneg_L2`.) -/
theorem lambdaCore_nonneg_rect (M : Fin 3 → ℕ) : 0 ≤ lambdaCore M := lambdaCore_nonneg_L2 M

/-! ## §5 — the `ℝ≥0∞` form (the shape `D1PerVChartObligation.hCore` consumes) -/

/-- **§5 — the `ℝ≥0∞` form of the rectangular arithmetic lemma.** With `coreDeepest =
ofReal(lambdaCore M)` (rectangular deepest widths `M = H − r`) and the degraded-core value
`ofReal(lambdaCore M')`,

    coreDeepest ≤ (extra : ℝ≥0∞)/2 + ofReal(lambdaCore M').

Bridges the `ℚ` lemma through `ENNReal.ofReal` (both `lambdaCore`s nonneg; `(extra:ℝ≥0∞)/2 =
ofReal((extra:ℝ)/2)`). This is the `hCore` arithmetic in the units the middle-stratum chart producer
needs — `coreDeepest = ofReal(lambdaCore (fun s => H s − r))` is EXACTLY the
`D1PerVChartObligation.hCore` deepest-core value (`RouteMD1ForallV`:95). -/
theorem coreDeepest_le_extraRect_half_add_lambdaCore_MprimeRect (M : Fin 3 → ℕ) (a b : ℕ)
    (ha : a ≤ M 0) (hab : a + b ≤ M 1) (hb : b ≤ M 2) :
    ENNReal.ofReal (lambdaCore M : ℝ)
      ≤ (extraRect M a b : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (MprimeRect M a b) : ℝ) := by
  have hQ := lambdaCore_le_extraRect_half_add_lambdaCore_MprimeRect M a b ha hab hb
  -- nonnegativity of the two cores + `extra/2`
  have hMnn : (0 : ℚ) ≤ lambdaCore M := lambdaCore_nonneg_rect _
  have hpnn : (0 : ℚ) ≤ lambdaCore (MprimeRect M a b) := lambdaCore_nonneg_rect _
  have hext2 : (0 : ℝ) ≤ (extraRect M a b : ℝ) / 2 := by positivity
  -- rewrite `(extra:ℝ≥0∞)/2` as `ofReal((extra:ℝ)/2)`
  have hof2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num
  have hbridge : (extraRect M a b : ℝ≥0∞) / 2 = ENNReal.ofReal ((extraRect M a b : ℝ) / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_natCast, hof2]
  rw [hbridge, ← ENNReal.ofReal_add hext2 (by exact_mod_cast hpnn)]
  apply ENNReal.ofReal_le_ofReal
  -- the `ℝ` form of the `ℚ` inequality (cast `ℚ → ℝ`, monotone)
  have hQR : (lambdaCore M : ℝ)
      ≤ (extraRect M a b : ℝ) / 2 + (lambdaCore (MprimeRect M a b) : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hQ
    push_cast at hcast
    linarith [hcast]
  linarith [hQR]

end DLNFibre.DLN.RLCT
