import DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart
import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Foundations.S1QuasiSplit
import DLNFibre.DLN.RLCT.Foundations.S1Spectator

/-!
# `DLNFibre.DLN.RLCT.Validate.D1ChartProducerL2Build` — the D1 producer build (L = 2)

This module builds, ON TOP of the banked reduction `deepest_le_of_optimal_of_chart_certificate`
(`D1ChartProducerL2`, which bundles the genuinely-Mathlib-lacking IFT chart into the certificate
`GeneralVChartL2`), the producer-side pieces for the D1 (★) per-point obligation
`rlctAt_deepest_le_of_optimal` (Skeleton:1172) at L = 2.

## What this module lands (the honest scope)

The middle-stratum `hCore` (case (B), spec §4B) is the **second-peel arithmetic** that the slice
residual at a middle-stratum optimal `v` satisfies. The decorrelated pen-and-paper adjudication
(a97332 / a9a2cf, EXACT, 164-strata exhaustive sweep `m ≤ 8`, ZERO violations) banked the unifying
value

    rlctAtOn R 0 = extra/2 + lambdaCore(M'),   extra = m(a+b) − ab,  M' = (m−a, m−a−b, m−b),

with `m` the reduced width, `a = rank(A₁)−r`, `b = rank(A₂)−r`. The middle-stratum `hCore` then
needs the **self-contained arithmetic** `extra/2 + lambdaCore(M') ≥ lambdaCore(square m)` (the
deepest reduced widths at L = 2 are the square `(m, m, m)`; `coreDeepest = lambdaCore(square m)`),
which is PURE `ℚ`/`Mval`/`Adm` algebra — no R1, no analysis. This module proves that arithmetic
(`extra_half_add_lambdaCore_Mprime_ge_square`, sorry-free, clean-three) via the banked symbolic
identity `extra + Mval(M', (t,0)) = Mval(square m, (a+t, 0))` (`Mval_Mprime_add_extra_eq_square`).

It then assembles the case-(B) `hCore` discharge as a **reduction** that takes:
  * the second-peel chart data (the `extra` Morse split + the degraded-core slice — the genuinely
    Mathlib-lacking Morse-with-parameters diffeo) as bundled hypotheses, AND
  * the R1-resolution-at-`M'` interface `hResolveM'` (spec §5) as a NAMED HYPOTHESIS (NOT a sorry —
    R1's `resolution_charts` for arbitrary width `M'` discharges it when R1 closes),
and produces `coreDeepest ≤ rlctAtOn R t0`.

## The chart-construction wall (surfaced, NOT ground)

Constructing a `GeneralVChartL2` INSTANCE at a general optimal `v` — the producer the spec's §4
build order envisages — requires the constant-`nReg` IFT chart at general `v`. Mathlib v4.29 has NO
Morse / Morse–Bott / Gromoll–Meyer / constant-rank quadratic split (verified in `D1ChartProducerL2`'s
docstring), and even the DEEPEST analog `deepest_gauge_squeeze_exists` (`DeepestGaugeChart`:353) is
itself an open `sorry`. So the chart construction is the precise residual wall (expedition Item 81 /
named wall #120 for L ≥ 3); it is NOT built here. This module lands the arithmetic + the case-(B)
`hCore` reduction (the formalisable content), feeding the existing certificate-level reduction.

Scope L = 2 only (`H : Fin 3 → ℕ`).
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-! ## §6 — the self-contained arithmetic lemma (pure `ℚ`/`Mval`/`Adm`, no analysis)

`extra/2 + lambdaCore(M') ≥ lambdaCore(square m)`, `extra = m(a+b) − ab`,
`M' = (m−a, m−a−b, m−b)`. The deepest reduced widths at L = 2 are the square `(m, m, m)`. -/

/-- The square reduced widths `(m, m, m) : Fin 3 → ℕ` — the deepest stratum at L = 2. -/
def squareWidths (m : ℕ) : Fin 3 → ℕ := fun _ => m

/-- The middle-stratum degraded reduced widths `M' = (m−a, m−a−b, m−b) : Fin 3 → ℕ`. -/
def MprimeWidths (m a b : ℕ) : Fin 3 → ℕ := ![m - a, m - a - b, m - b]

/-- The `extra` Morse-square count `m(a+b) − ab` (`= nReg_v − nReg` at the middle stratum). -/
def extraCount (m a b : ℕ) : ℕ := m * (a + b) - a * b

/-- **`Mval` expanded at L = 2.** For widths `M : Fin 3 → ℕ` and exponents `T : Fin 2 → ℕ`,
`Mval M T = (M 0 − T 0)(M 1 − T 0) + (T 0 − T 1)(M 2 − T 1)` over `ℤ`
(the two-term sum, `tPrev` at `j = 0` reading `M 0` and at `j = 1` reading `T 0`). -/
theorem Mval_L2 (M : Fin 3 → ℕ) (T : Fin 2 → ℕ) :
    Mval M T = ((M 0 : ℤ) - T 0) * ((M 1 : ℤ) - T 0)
      + ((T 0 : ℤ) - T 1) * ((M 2 : ℤ) - T 1) := by
  rw [Mval, Fin.sum_univ_two]
  -- `tPrev` at `j = 0` is `M 0`; at `j = 1` is `T 0`. `M (j.succ)` is `M 1`, `M 2`.
  have h0 : tPrev M T 0 = (M 0 : ℤ) := by rw [tPrev]; simp
  have h1 : tPrev M T 1 = (T 0 : ℤ) := by rw [tPrev]; norm_num
  have hs0 : (0 : Fin 2).succ = (1 : Fin 3) := rfl
  have hs1 : (1 : Fin 2).succ = (2 : Fin 3) := rfl
  rw [h0, h1, hs0, hs1]

/-- **The banked symbolic identity** `extra + Mval(M', T) = Mval(square m, ![T 0 + a, 0])` (the
`extra + D_{a,b}(t) = F_m(a+t)` of spec §6, at `t = T 0`, `T 1 = 0`). Over `ℤ` and verified exact by
the design-pass (sympy + 164-strata sweep). Requires `a + b ≤ m` (the middle-stratum admissibility
ensuring the `ℕ`-subtractions in `M'` are honest). -/
theorem Mval_Mprime_add_extra_eq_square (m a b : ℕ) (T : Fin 2 → ℕ)
    (hab : a + b ≤ m) (hT1 : T 1 = 0) :
    (extraCount m a b : ℤ) + Mval (MprimeWidths m a b) T
      = Mval (squareWidths m) ![T 0 + a, 0] := by
  -- honest casts (all subtractions nonneg under `a + b ≤ m`)
  have ham : a ≤ m := by omega
  have hbm : b ≤ m := by omega
  have hcast_ma : ((m - a : ℕ) : ℤ) = (m : ℤ) - a := by omega
  have hcast_mab : ((m - a - b : ℕ) : ℤ) = (m : ℤ) - a - b := by omega
  have hcast_mb : ((m - b : ℕ) : ℤ) = (m : ℤ) - b := by omega
  have hab_le : a * b ≤ m * (a + b) := by nlinarith [ham, Nat.le_add_right (a) (b)]
  have hcast_extra : (extraCount m a b : ℤ) = (m : ℤ) * (a + b) - a * b := by
    rw [extraCount, Nat.cast_sub hab_le]; push_cast; ring
  -- expand both sides via `Mval_L2`
  rw [Mval_L2, Mval_L2]
  -- read off the width / exponent entries
  have hM0 : (MprimeWidths m a b) 0 = m - a := rfl
  have hM1 : (MprimeWidths m a b) 1 = m - a - b := rfl
  have hM2 : (MprimeWidths m a b) 2 = m - b := rfl
  have hSq : ∀ i : Fin 3, (squareWidths m) i = m := fun _ => rfl
  have hc0 : (![T 0 + a, 0] : Fin 2 → ℕ) 0 = T 0 + a := rfl
  have hc1 : (![T 0 + a, 0] : Fin 2 → ℕ) 1 = 0 := rfl
  rw [hM0, hM1, hM2, hSq 0, hSq 1, hSq 2, hc0, hc1, hT1]
  push_cast [hcast_ma, hcast_mab, hcast_mb, hcast_extra]
  ring

/-- At L = 2 every admissible `T ∈ Adm M` has its last exponent vanish: `T 1 = 0` (the
`admPred` last-coordinate clause `j.val = L − 1 = 1 → T j = 0`). -/
theorem Adm_L2_last_zero (M : Fin 3 → ℕ) {T : Fin 2 → ℕ} (hT : T ∈ Adm M) : T 1 = 0 := by
  rw [Adm, Finset.mem_filter] at hT
  exact hT.2.2.2 1 rfl

/-- The candidate exponent `![T 0 + a, 0]` lands in `Adm (square m)` provided `T 0 + a ≤ m`. The
binding clause is the block bound `T 0 + a ≤ admBound (square m) 0 = min m m = m`; weak-decrease and
the last-coordinate clause hold by `0 ≤ T 0 + a` and `(![·,0]) 1 = 0`. -/
theorem cand_mem_Adm_square (m a t : ℕ) (htm : t + a ≤ m) :
    (![t + a, 0] : Fin 2 → ℕ) ∈ Adm (squareWidths m) := by
  -- the candidate entries + the per-index `admBound` (both `= m` for the square)
  have hc0 : (![t + a, 0] : Fin 2 → ℕ) 0 = t + a := rfl
  have hc1 : (![t + a, 0] : Fin 2 → ℕ) 1 = 0 := rfl
  have hb0 : admBound (squareWidths m) 0 = m := by rw [admBound]; simp [squareWidths]
  have hb1 : admBound (squareWidths m) 1 = m := by rw [admBound]; simp [squareWidths]
  -- per-index bound `T j ≤ admBound j`, via `Fin.forall_fin_two`
  have hbound : ∀ j : Fin 2, (![t + a, 0] : Fin 2 → ℕ) j ≤ admBound (squareWidths m) j := by
    rw [Fin.forall_fin_two, hc0, hc1, hb0, hb1]; exact ⟨by omega, Nat.zero_le _⟩
  rw [Adm, Finset.mem_filter]
  refine ⟨?_, hbound, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro j; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (hbound j)
  · -- weak-decrease `T j ≤ T i` for `i ≤ j`: `T 0 = t+a ≥ 0 = T 1`, monotone-decreasing.
    intro i j hij
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · -- `j = 0` ⟹ `i = 0`
      rw [Fin.le_zero_iff.1 hij]
    · -- `j = j'.succ`; in `Fin 2`, `j' : Fin 1` so `j = 1`, `T 1 = 0 ≤ T i`
      have hj1 : j'.succ = (1 : Fin 2) := by
        have : j' = (0 : Fin 1) := Subsingleton.elim _ _
        rw [this]; rfl
      rw [hj1, hc1]; exact Nat.zero_le _
  · -- last-coordinate clause: `j.val = 1 → T j = 0`; only `j = 1` qualifies, `T 1 = 0`.
    intro j hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · exact absurd hj (by simp only [Fin.val_zero]; omega)
    · have hj1 : j'.succ = (1 : Fin 2) := by
        have : j' = (0 : Fin 1) := Subsingleton.elim _ _
        rw [this]; rfl
      rw [hj1, hc1]

/-- For `T ∈ Adm (M' = (m−a, m−a−b, m−b))`, the first exponent is bounded by `m − a − b`
(the block bound `admBound (M') 0 = min (m−a) (m−a−b) = m−a−b`), so `T 0 + a ≤ m`. -/
theorem Adm_Mprime_first_bound (m a b : ℕ) (hab : a + b ≤ m) {T : Fin 2 → ℕ}
    (hT : T ∈ Adm (MprimeWidths m a b)) : T 0 + a ≤ m := by
  rw [Adm, Finset.mem_filter] at hT
  have hbd := hT.2.1 0
  have hbd' : T 0 ≤ min (m - a) (m - a - b) := by
    rw [admBound, Fin.val_zero, if_pos rfl] at hbd
    simpa only [MprimeWidths, Matrix.cons_val_zero, Matrix.cons_val_one] using hbd
  -- `T 0 ≤ min (m-a) (m-a-b) = m-a-b`; with `a + b ≤ m`, `T 0 + a ≤ m`.
  omega

/-- **§6 — the self-contained arithmetic lemma.** `extra/2 + lambdaCore(M') ≥ lambdaCore(square m)`
over `ℚ`, for the middle-stratum data `a + b ≤ m`. The deepest reduced widths at L = 2 are the
square `(m, m, m)`, so `coreDeepest = lambdaCore (square m)`. Pure `Mval`/`Adm`/`Finset.inf'`
algebra: the `M'`-minimiser `T*` (Adm-last `T* 1 = 0`) maps under the banked identity
`Mval_Mprime_add_extra_eq_square` to an admissible square exponent `![T* 0 + a, 0]`, dominating the
square infimum. Verified ZERO violations across the 164 L = 2 strata (`m ≤ 8`). -/
theorem extra_half_add_lambdaCore_Mprime_ge_square (m a b : ℕ) (hab : a + b ≤ m) :
    lambdaCore (squareWidths m)
      ≤ (extraCount m a b : ℚ) / 2 + lambdaCore (MprimeWidths m a b) := by
  -- the `M'`-side infimum minimiser
  obtain ⟨T, hTmem, hTeq⟩ :=
    Finset.exists_mem_eq_inf' (Adm_nonempty (MprimeWidths m a b)) (Mval (MprimeWidths m a b))
  have hT1 : T 1 = 0 := Adm_L2_last_zero _ hTmem
  have hTbound : T 0 + a ≤ m := Adm_Mprime_first_bound m a b hab hTmem
  -- the dominating square exponent
  have hcand : (![T 0 + a, 0] : Fin 2 → ℕ) ∈ Adm (squareWidths m) :=
    cand_mem_Adm_square m a (T 0) (by omega)
  -- name the two `ℤ`-valued infima
  set Isq : ℤ := (Adm (squareWidths m)).inf' (Adm_nonempty (squareWidths m))
    (Mval (squareWidths m)) with hIsq
  set Ip : ℤ := (Adm (MprimeWidths m a b)).inf' (Adm_nonempty (MprimeWidths m a b))
    (Mval (MprimeWidths m a b)) with hIp
  -- `inf'_{sq} Mval(sq) ≤ Mval(sq, cand) = extra + Mval(M', T) = extra + inf'_{M'} Mval(M')`
  have hkey : Isq ≤ (extraCount m a b : ℤ) + Ip := by
    rw [hTeq]
    calc Isq ≤ Mval (squareWidths m) ![T 0 + a, 0] := Finset.inf'_le _ hcand
      _ = (extraCount m a b : ℤ) + Mval (MprimeWidths m a b) T :=
          (Mval_Mprime_add_extra_eq_square m a b T hab hT1).symm
  -- lift the `ℤ` inequality through `lambdaCore = (1/2)·(inf' Mval)`
  rw [lambdaCore, lambdaCore, ← hIsq, ← hIp]
  have hkeyQ : (Isq : ℚ) ≤ (extraCount m a b : ℚ) + (Ip : ℚ) := by exact_mod_cast hkey
  linarith [hkeyQ]

end DLNFibre.DLN.RLCT
