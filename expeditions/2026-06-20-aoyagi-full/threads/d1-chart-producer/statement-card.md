# Statement card — D1 chart-producer build (L = 2)

Module: `lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean` @ `bb76d5bc`
(branch `d1-chart-producer-l2build`, off `origin/expedition/aoyagi-full`).
Status: **sorry-free**, all theorems clean-three `[propext, Classical.choice, Quot.sound]`
(verified by `#print axioms`; no `monomial_rlct`, no `sorryAx`, no `native_decide`).

This thread builds the formalisable producer-side content for the D1 (★) per-point obligation
`rlctAt_deepest_le_of_optimal` (Skeleton:1172) at L = 2 — the arithmetic lemma (§6), the case-(B)
`hCore` reduction (the second-peel engine + the §5 interface), and the middle-stratum producer
assembly. The `GeneralVChartL2` construction at general `v` (the IFT chart) is the surfaced chart
wall, NOT built here.

---

## §6 — the arithmetic lemma

> **Claim.** For middle-stratum data `a + b ≤ m`, `extra/2 + lambdaCore(M') ≥ lambdaCore(square m)`
> over `ℚ`, where `extra = m(a+b) − ab`, `M' = (m−a, m−a−b, m−b)`, `square m = (m,m,m)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.extra_half_add_lambdaCore_Mprime_ge_square`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean` @ `bb76d5bc`)
> - **Gloss.** `lambdaCore (squareWidths m) ≤ (extraCount m a b : ℚ)/2 + lambdaCore (MprimeWidths m a b)`,
>   under `hab : a + b ≤ m`. `lambdaCore = ½·min_{T∈Adm} Mval`.
> - **Proved.** Unconditionally over `ℚ`. The `M'`-minimiser `T*` (with `T* 1 = 0` by the L = 2 Adm
>   last-coordinate clause) maps under the banked identity `Mval_Mprime_add_extra_eq_square`
>   (`extra + Mval(M', T) = Mval(square m, ![T 0 + a, 0])`, sympy-verified exact) to an admissible
>   square exponent `![T* 0 + a, 0] ∈ Adm (square m)` (`cand_mem_Adm_square`, needs `T* 0 + a ≤ m`,
>   from `Adm_Mprime_first_bound`), dominating the square `Finset.inf'`.
>   Helper lemmas: `Mval_L2` (the two-term `Mval` expansion at L = 2), `Adm_L2_last_zero`,
>   `Adm_Mprime_first_bound`. ENNReal form: `coreDeepest_le_extra_half_add_lambdaCore_Mprime`
>   (bridges through `ENNReal.ofReal`, uses `lambdaCore_nonneg_L2`).
> - **Assumed.** `a + b ≤ m` (so `M'` widths are honest `ℕ`-subtractions; the middle-stratum
>   admissibility).
> - **Cited.** none (pure `Mval`/`Adm`/`Finset.inf'` algebra; `Mval_nonneg_of_adm` reused from
>   Skeleton for `lambdaCore_nonneg_L2`).
> - **Deferred.** none (this piece is complete).
> - **Structure & ideas observed (pen-and-paper a97332/a9a2cf, decorrelated).** The unifying value
>   `rlctAtOn R 0 = extra/2 + lambdaCore(M')` across the whole L = 2 (m,a,b) design space (164-strata
>   sweep `m ≤ 8`, ZERO violations); the load-bearing symbolic identity `extra + D_{a,b}(t) =
>   F_m(a+t)`, `F_m(s) = (m−s)² + sm` (104 equality / 60 strict; D1 needs only `≥`). `m` is a SINGLE
>   reduced width (square deepest).
> - **Route (controller spec §6).** Land first (cleanest; no chart, no analysis). At L = 2 `Adm` is
>   small; the `Finset.inf'`-domination route (minimiser `T*` → admissible square candidate) replaced
>   the `decide`-per-case suggestion (`m` is unbounded).
> - **Status.** sorry-free.

---

## §4B — the case-(B) `hCore` reduction (second peel + interface)

> **Claim.** At a middle-stratum optimal `v` (square deepest, `coreDeepest = ofReal(lambdaCore (square
> m))`): given the second-peel chart data (`F₂ = ∑_{extra} s² + Q₂`, slice residual `R₂`, comparison)
> and the §5 R1-resolution-at-`M'` interface value `hDegraded : rlctAtOn R₂ t0₂ = ofReal(lambdaCore
> M')`, the D1 `hCore` holds: `coreDeepest ≤ rlctAtOn R t0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.hCore_middle_stratum_of_interface`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean` @ `bb76d5bc`)
> - **Gloss.** Applies the SECOND `rlct_quasiSplit_ge` to `R` (post-second-chart form `F₂`), giving
>   `extra/2 + rlctAtOn R₂ t0₂ ≤ rlctAtOn F₂ (0,t0₂) = rlctAtOn R t0`; then `hDegraded` +
>   `coreDeepest_le_extra_half_add_lambdaCore_Mprime` close `coreDeepest ≤ rlctAtOn R t0`.
> - **Proved.** The `rlct_quasiSplit_ge` application + the arithmetic combine is PROVED here.
> - **Assumed (named hypotheses, the genuinely-unbuilt analytic content — NOT sorries).** The
>   second-peel chart transfer `hchart₂`, the post-chart form `hF₂`, `hQ₂0`, `hR₂`/`hR₂ne`, the
>   comparison `hcmp₂` (the Morse-with-parameters local diffeo Mathlib lacks); the §5 interface value
>   `hDegraded`; `coreDeepest = ofReal(lambdaCore (square m))`; `a + b ≤ m`.
> - **Cited.** the banked `rlct_quasiSplit_ge` (S1QuasiSplit, clean-three).
> - **Deferred.** the second-peel chart DATA construction (the Morse-with-params diffeo) — part of
>   the chart wall below. `hDegraded` discharges when R1's general resolution at the rectangular `M'`
>   closes (`R1ResolutionInterface` + `r1_interface_discharges_degraded` pin the contract).
> - **Status.** sorry-free (conditional on the named hypotheses).

### §5 interface contract

`R1ResolutionInterface : Prop` — `∀ M : Fin 3 → ℕ, (∀ s, 0 < M s) → rlctAtOn (dlnLoss M 0)
(fun _ => 0) = ofReal(lambdaCore M)`. `r1_interface_discharges_degraded` shows it discharges
`hDegraded` at the rectangular `M'` (provided `∀ s, 0 < M' s`). BINDING CONSTRAINT (recorded):
`resolution_charts` (Skeleton:1228) must stay general-width (`hMid` only) to cover `M'`.

---

## §4B (assembly) — the middle-stratum producer

> **Claim.** At a middle-stratum optimal `v` (square deepest widths): the FIRST `nReg`-peel data + the
> deepest `#44` equality `hDeepest` + the SECOND-peel data + the §5 interface ⟹ `rlctAt deepest ≤
> rlctAt v` (the case-(B) per-point D1 `≥`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepest_le_of_optimal_middle_stratum`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2Build.lean` @ `bb76d5bc`)
> - **Gloss.** Discharges `hCore` from `hCore_middle_stratum_of_interface` (NOT a bare hypothesis),
>   then wires the banked `deepest_le_of_optimal_chart` (FIRST peel `hAtV` via
>   `rlctAt_ge_nReg_add_slice` + `hDeepest` + `hCore`). `nReg = nRegL2 H r`, `extra = extraCount m a b`.
> - **Proved.** The full assembly given the chart data.
> - **Assumed (named hypotheses).** Both peels' chart data (genuinely unbuilt) + `hDeepest` (= #44,
>   `deepest_regular_core_normal_form`, the tracked Skeleton sorry) + the §5 interface value;
>   `a + b ≤ m`; square deepest `coreDeepest = ofReal(lambdaCore (square m))`.
> - **Cited.** banked `deepest_le_of_optimal_chart`, `rlctAt_ge_nReg_add_slice`, `rlct_quasiSplit_ge`.
> - **Deferred.** the chart-data construction at general `v` (the wall); `hDeepest` (#44).
> - **Status.** sorry-free (conditional on the named hypotheses).

---

## The chart-construction wall (surfaced, NOT ground)

Constructing a `GeneralVChartL2` INSTANCE at a general optimal `v` (the producer the spec's §4
build order envisages, which would close `rlctAt_deepest_le_of_optimal` outright) requires the
constant-`nReg` IFT chart at general `v`. Mathlib v4.29 has NO Morse / Morse–Bott / Gromoll–Meyer /
constant-rank quadratic split (verified, `D1ChartProducerL2` docstring), and even the DEEPEST analog
`deepest_gauge_squeeze_exists` (`DeepestGaugeChart`:353) is itself an open `sorry`. So the chart
construction (Item 81 / named wall #120 for L ≥ 3) is NOT built here. The minimal residual to close
the case-(B) per-point D1 `≥`:

1. The **first-peel chart** at general `v` — the constant-`nReg` IFT chart producing the slice
   residual `R` with `rlctAt v = rlctAtOn F (0,t0)`, `F = ∑_{nReg} s² + Q` (the `rlctAt_ge_nReg_add_slice`
   inputs). Strictly harder than the still-open deepest analog `deepest_gauge_squeeze_exists`.
2. The **second-peel (Morse-with-parameters) chart** of `R` — `R` brings to `F₂ = ∑_{extra} s² + Q₂`
   with the degraded-core residual `R₂` (the `hCore_middle_stratum_of_interface` inputs).
3. The **degraded-core identification** `rlctAtOn R₂ t0₂ = ofReal(lambdaCore M')` — the §5 interface,
   dischargeable from R1's general resolution at `M'` (R1's `resolution_charts` is itself gated).

Case (A) (deepest-type) is the existing `deepest_le_of_optimal_of_chart_certificate`
(`D1ChartProducerL2`): given a `GeneralVChartL2` certificate it lands the conclusion unconditionally
(modulo `hDeepest` = #44). Case (A)'s `hCore` is the `hRform` factorization (FALSE at middle strata —
the SPLIT verdict), so the A/B dispatch is genuinely two-pronged, not one `GeneralVChartL2`.

## Scope

L = 2 only. Square deepest reduced widths `(m,m,m)` (covering square `H = (m+r, m+r, m+r)`), per the
banked adjudication's single-`m` parameterization. Non-square `H` at L = 2 (non-square `H − r`,
outside the single-`m` `M'`-formula) is beyond the banked adjudication. General-L is wall #120.
