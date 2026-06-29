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
Morse / Morse–Bott / Gromoll–Meyer / constant-rank quadratic split (verified in
`D1ChartProducerL2`'s docstring), and even the DEEPEST analog `deepest_gauge_squeeze_exists`
(`DeepestGaugeChart`:353) is itself an open `sorry`. So the chart construction is the precise
residual wall (expedition Item 81 / named wall #120 for L ≥ 3); it is NOT built here. This module
lands the arithmetic + the case-(B) `hCore` reduction (the formalisable content), feeding the
existing certificate-level reduction.

Scope L = 2 only (`H : Fin 3 → ℕ`). The banked adjudication parameterizes the middle stratum by a
SINGLE reduced width `m` (square deepest widths `(m, m, m)`, covering square `H = (m+r, m+r, m+r)`);
the §6 arithmetic and the case-(B) reduction are stated at that square-deepest scope. (Non-square
`H` at L = 2 has non-square deepest widths `H − r` outside the single-`m` `M'`-formula — beyond the
banked adjudication.)
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

/-- `lambdaCore M ≥ 0` (admissible `Mval ≥ 0` on the cone ⟹ `inf' ≥ 0`). Reuses the banked
`Mval_nonneg_of_adm`; stated at L = 2 (`hL : 1 ≤ 2` is automatic). -/
theorem lambdaCore_nonneg_L2 (M : Fin 3 → ℕ) : 0 ≤ lambdaCore M := by
  rw [lambdaCore]
  have hge : 0 ≤ (Adm M).inf' (Adm_nonempty M) (Mval M) :=
    Finset.le_inf' _ _ (fun T hT => Mval_nonneg_of_adm M T hT (by norm_num))
  positivity

/-- **§6 — the `ℝ≥0∞` form of the arithmetic lemma** (the shape the RLCT chain consumes). With
`coreDeepest = ofReal(lambdaCore (square m))` and the degraded-core value `ofReal(lambdaCore M')`,

    coreDeepest ≤ (extra : ℝ≥0∞)/2 + ofReal(lambdaCore M').

Bridges the `ℚ` lemma through `ENNReal.ofReal` (both `lambdaCore`s nonneg; `(extra:ℝ≥0∞)/2 =
ofReal((extra:ℝ)/2)`). This is the `hCore` arithmetic in the units `rlct_quasiSplit_ge` produces. -/
theorem coreDeepest_le_extra_half_add_lambdaCore_Mprime (m a b : ℕ) (hab : a + b ≤ m) :
    ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ)
      ≤ (extraCount m a b : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ) := by
  have hQ := extra_half_add_lambdaCore_Mprime_ge_square m a b hab
  -- nonnegativity of the two cores + `extra/2`
  have hsqnn : (0 : ℚ) ≤ lambdaCore (squareWidths m) := lambdaCore_nonneg_L2 _
  have hpnn : (0 : ℚ) ≤ lambdaCore (MprimeWidths m a b) := lambdaCore_nonneg_L2 _
  have hext2 : (0 : ℝ) ≤ (extraCount m a b : ℝ) / 2 := by positivity
  -- rewrite `(extra:ℝ≥0∞)/2` as `ofReal((extra:ℝ)/2)`
  have hof2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num
  have hbridge : (extraCount m a b : ℝ≥0∞) / 2 = ENNReal.ofReal ((extraCount m a b : ℝ) / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_natCast, hof2]
  rw [hbridge, ← ENNReal.ofReal_add hext2 (by exact_mod_cast hpnn)]
  apply ENNReal.ofReal_le_ofReal
  -- the `ℝ` form of the `ℚ` inequality (cast `ℚ → ℝ`, monotone)
  have hQR : (lambdaCore (squareWidths m) : ℝ)
      ≤ (extraCount m a b : ℝ) / 2 + (lambdaCore (MprimeWidths m a b) : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hQ
    push_cast at hcast
    linarith [hcast]
  linarith [hQR]

/-! ## §4B — the middle-stratum `hCore` discharge (the SECOND-PEEL engine application + interface)

At a middle-stratum optimal `v` (`nReg_v > nReg`), the constant-`nReg` slice residual `R` itself
admits a SECOND constant-rank peel (the Morse-with-parameters local diffeo, design-pass a9a2cf):
`R` brings into the post-(second-)chart form `F₂ = ∑_{extra} s² + Q₂` over `(Fin extra → ℝ) × Y₂`,
with the degraded-core residual `R₂ = Q₂(0,·)` on `Y₂` (RLCT-equal to the deepest DLN core of the
rectangular widths `M' = (m−a, m−a−b, m−b)`). The SECOND `rlct_quasiSplit_ge` then gives

    extra/2 + rlctAtOn R₂ t0₂ ≤ rlctAtOn R t0,

and the §5 R1-resolution-at-`M'` interface (`hDegraded`) supplies `rlctAtOn R₂ t0₂ =
ofReal(lambdaCore M')`. Combined with the §6 arithmetic
(`coreDeepest_le_extra_half_add_lambdaCore_Mprime`)
and `coreDeepest = ofReal(lambdaCore (square m))`, this gives `coreDeepest ≤ rlctAtOn R t0` — the
case-(B) `hCore`. The second-peel chart DATA is the genuinely-unbuilt Morse-with-parameters content
(taken as hypotheses, NOT sorries); the `rlct_quasiSplit_ge` application + the arithmetic are the
formalisable content this theorem PROVES. -/

/-- **Case-(B) `hCore` via the second peel + the R1-resolution interface.** For the middle-stratum
data `a + b ≤ m`: given the second-peel chart transfer (`hchart₂ : rlctAtOn R t0 = rlctAtOn F₂
(0,t0₂)`), the post-(second-)chart sum-of-squares form `F₂ = ∑_{extra} s² + Q₂` with its slice
residual `R₂ = Q₂(0,·)` (measurable a.e.-nonzero) and quasi-split comparison `hcmp₂`, the
degraded-core value `hDegraded : rlctAtOn R₂ t0₂ = ofReal(lambdaCore M')` (the §5 interface
specialized — R1's general resolution at the rectangular `M'`), and
`coreDeepest = ofReal(lambdaCore (square m))`,
the D1 `hCore` holds: `coreDeepest ≤ rlctAtOn R t0`. The `extra` Morse squares peeled in the SECOND
engine pass are `extraCount m a b = m(a+b) − ab`. -/
theorem hCore_middle_stratum_of_interface {Y₂ : Type*}
    [PseudoMetricSpace Y₂] [MeasureSpace Y₂] [ProperSpace Y₂]
    [IsFiniteMeasureOnCompacts (volume : Measure Y₂)] [BorelSpace Y₂]
    {Y : Type*} [MeasureSpace Y] [TopologicalSpace Y] (R : Y → ℝ) (t0 : Y)
    (m a b : ℕ) (hab : a + b ≤ m) (coreDeepest : ℝ≥0∞)
    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
    (F₂ : (Fin (extraCount m a b) → ℝ) × Y₂ → ℝ) (Q₂ : (Fin (extraCount m a b) → ℝ) × Y₂ → ℝ)
    (R₂ : Y₂ → ℝ) (t0₂ : Y₂)
    (hchart₂ : rlctAtOn R t0 = rlctAtOn F₂ ((0 : Fin (extraCount m a b) → ℝ), t0₂))
    (hF₂ : ∀ p, F₂ p = (∑ i, p.1 i ^ 2) + Q₂ p)
    (hQ₂0 : ∀ p, 0 ≤ Q₂ p) (hF₂meas : Measurable F₂)
    (hR₂ : ∀ t, R₂ t = Q₂ (0, t)) (hR₂meas : Measurable R₂)
    (hR₂ne : ∃ U ∈ 𝓝 t0₂, ∀ᵐ z ∂(volume.restrict U), R₂ z ≠ 0)
    (C : ℝ) (hC : 0 < C)
    (hcmp₂ : ∃ U ∈ 𝓝 ((0 : Fin (extraCount m a b) → ℝ), t0₂), ∀ p ∈ U,
        (∑ i, p.1 i ^ 2) + R₂ p.2 ≤ C * F₂ p)
    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
    coreDeepest ≤ rlctAtOn R t0 := by
  -- the SECOND quasi-split engine pass on `R` (peel the `extra` Morse squares)
  have hpeel : (extraCount m a b : ℝ≥0∞) / 2 + rlctAtOn R₂ t0₂
      ≤ rlctAtOn F₂ ((0 : Fin (extraCount m a b) → ℝ), t0₂) :=
    rlct_quasiSplit_ge F₂ Q₂ R₂ t0₂ hF₂ hQ₂0 hF₂meas hR₂ hR₂meas hR₂ne C hC hcmp₂
  -- rewrite via the chart transfer + the interface value
  rw [hchart₂]
  refine le_trans ?_ hpeel
  rw [hDegraded, hcoreDeepest]
  exact coreDeepest_le_extra_half_add_lambdaCore_Mprime m a b hab

/-! ## §5 — the R1-resolution-at-`M'` interface (the named-hypothesis contract)

The `hDegraded` hypothesis of `hCore_middle_stratum_of_interface` is the §5 interface specialized
to the degraded-core slice `R₂`. The spec's exact interface — R1's general resolution at the
rectangular `M'` — is the `R1ResolutionInterface` predicate below; when the second-peel
degraded-core slice IS the literal DLN core `dlnLoss M' 0` at its deepest point `(0 : Params M')`,
the interface
discharges `hDegraded` directly (`r1_interface_discharges_degraded`).

★ BINDING CONSTRAINT (recorded): `resolution_charts` (Skeleton:1228) MUST stay general-width
(`hMid : ∀ s, 0 < M' s`, NOT narrowed to square-only) so it covers the rectangular `M'`. The
interface is dischargeable from the banked `resolution_value_of_atlas` (ResolutionAtlas:197) +
`resolution_charts` for arbitrary width (both verified general-width); R1's resolution closing
supplies it. -/

/-- **The R1-resolution-at-`M'` interface (spec §5).** R1's general resolution at the (rectangular)
reduced widths `M : Fin 3 → ℕ` with all layers nondegenerate (`hMid`): the deepest DLN core
`dlnLoss M 0` at the origin `(0 : Params M)` has local RLCT `ofReal(lambdaCore M)`. The
middle-stratum `hCore` consumes this at the degraded `M' = (m−a, m−a−b, m−b)`, NOT R1's closed-form
VALUE and NOT
#44 — so D1 sequences independently of R1's core value. -/
def R1ResolutionInterface : Prop :=
  ∀ (M : Fin 3 → ℕ), (∀ s, 0 < M s) →
    rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last 2))) ℝ) A)
        (fun _ => 0 : Params M)
      = ENNReal.ofReal (lambdaCore M : ℝ)

/-- The §5 interface discharges the `hDegraded` hypothesis when the second-peel degraded-core slice
is the literal DLN core `dlnLoss M' 0` on `Params M'` at its deepest point — provided `M'`'s layers
are all nondegenerate (`hMid'`, the R1 carve-out). -/
theorem r1_interface_discharges_degraded
    (hR1 : R1ResolutionInterface) (m a b : ℕ)
    (hMid' : ∀ s, 0 < MprimeWidths m a b s) :
    rlctAtOn (fun A : Params (MprimeWidths m a b) =>
        dlnLoss (MprimeWidths m a b)
          (0 : Matrix (Fin (MprimeWidths m a b 0))
            (Fin (MprimeWidths m a b (Fin.last 2))) ℝ) A) (fun _ => 0 : Params (MprimeWidths m a b))
      = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ) :=
  hR1 (MprimeWidths m a b) hMid'

/-! ## §4B (assembly) — the middle-stratum producer (the case-(B) per-point D1 `≥`)

Assembles the FIRST quasi-split peel (`rlctAt_ge_nReg_add_slice`, the `nReg`-block giving the
`hAtV` half) with the case-(B) `hCore` (`hCore_middle_stratum_of_interface`, the second peel +
the §5 interface + the §6 arithmetic) through the banked `deepest_le_of_optimal_chart`, landing the
D1 per-point `≥` at a middle-stratum optimal `v` (square deepest reduced widths `(m,m,m)`). The
first-peel chart data (the constant-`nReg` IFT chart producing the slice residual `R`) is the
genuinely-unbuilt analytic content — taken as hypotheses; the assembly is the formalisable
wiring. -/

/-- **The middle-stratum producer: case-(B) per-point D1 `≥`.** At a middle-stratum optimal `v`
(square deepest reduced widths `M = (m,m,m)`, `coreDeepest = ofReal(lambdaCore (square m))`), given
the FIRST-peel chart data (`hchart`/`hF`/`hQ0`/`hR`/`hRne`/`hcmp` on `(Fin nReg → ℝ) × Y`, the
`nReg`-block producing the slice residual `R`), the deepest-side `#44` equality `hDeepest`, AND the
SECOND-peel chart data + §5 interface (`hCore_middle_stratum_of_interface`'s inputs), the deepest
point has `≤` local RLCT than `v`: `rlctAt deepest ≤ rlctAt v`. The `hCore` is PROVED here (not a
bare hypothesis) from the second peel; `nReg = nRegL2 H r`, `extra = extraCount m a b`. -/
theorem deepest_le_of_optimal_middle_stratum
    {Y : Type*} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y]
    {Y₂ : Type*} [PseudoMetricSpace Y₂] [MeasureSpace Y₂] [ProperSpace Y₂]
    [IsFiniteMeasureOnCompacts (volume : Measure Y₂)] [BorelSpace Y₂]
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (deepest v : Params H) (m a b : ℕ) (hab : a + b ≤ m) (coreDeepest : ℝ≥0∞)
    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
    -- the FIRST-peel chart data (the `nReg`-block producing `R`)
    (F : (Fin (nRegL2 H r) → ℝ) × Y → ℝ) (Q : (Fin (nRegL2 H r) → ℝ) × Y → ℝ) (R : Y → ℝ) (t0 : Y)
    (hDeepest : rlctAt H (dlnLoss H B) deepest = (nRegL2 H r : ℝ≥0∞) / 2 + coreDeepest)
    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn F ((0 : Fin (nRegL2 H r) → ℝ), t0))
    (hF : ∀ p, F p = (∑ i, p.1 i ^ 2) + Q p)
    (hQ0 : ∀ p, 0 ≤ Q p) (hFmeas : Measurable F)
    (hR : ∀ t, R t = Q (0, t)) (hRmeas : Measurable R)
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U), R z ≠ 0)
    (Cc : ℝ) (hCc : 0 < Cc)
    (hcmp : ∃ U ∈ 𝓝 ((0 : Fin (nRegL2 H r) → ℝ), t0), ∀ p ∈ U,
        (∑ i, p.1 i ^ 2) + R p.2 ≤ Cc * F p)
    -- the SECOND-peel chart data + the §5 interface (discharging `hCore` on `R`)
    (F₂ : (Fin (extraCount m a b) → ℝ) × Y₂ → ℝ) (Q₂ : (Fin (extraCount m a b) → ℝ) × Y₂ → ℝ)
    (R₂ : Y₂ → ℝ) (t0₂ : Y₂)
    (hchart₂ : rlctAtOn R t0 = rlctAtOn F₂ ((0 : Fin (extraCount m a b) → ℝ), t0₂))
    (hF₂ : ∀ p, F₂ p = (∑ i, p.1 i ^ 2) + Q₂ p)
    (hQ₂0 : ∀ p, 0 ≤ Q₂ p) (hF₂meas : Measurable F₂)
    (hR₂ : ∀ t, R₂ t = Q₂ (0, t)) (hR₂meas : Measurable R₂)
    (hR₂ne : ∃ U ∈ 𝓝 t0₂, ∀ᵐ z ∂(volume.restrict U), R₂ z ≠ 0)
    (C₂ : ℝ) (hC₂ : 0 < C₂)
    (hcmp₂ : ∃ U ∈ 𝓝 ((0 : Fin (extraCount m a b) → ℝ), t0₂), ∀ p ∈ U,
        (∑ i, p.1 i ^ 2) + R₂ p.2 ≤ C₂ * F₂ p)
    (hDegraded : rlctAtOn R₂ t0₂ = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  -- discharge `hCore : coreDeepest ≤ rlctAtOn R t0` from the SECOND peel + the interface
  have hCore : coreDeepest ≤ rlctAtOn R t0 :=
    hCore_middle_stratum_of_interface R t0 m a b hab coreDeepest hcoreDeepest
      F₂ Q₂ R₂ t0₂ hchart₂ hF₂ hQ₂0 hF₂meas hR₂ hR₂meas hR₂ne C₂ hC₂ hcmp₂ hDegraded
  -- the banked per-point chart producer wiring (FIRST peel `hAtV` + `hCore` + `hDeepest`)
  exact deepest_le_of_optimal_chart H r B deepest v F Q R t0 coreDeepest
    hDeepest hchart hF hQ0 hFmeas hR hRmeas hRne Cc hCc hcmp hCore

end DLNFibre.DLN.RLCT
