# Scoping note — H_indep at general optimal `v` (the D1-at-general-`v` core)

**Verdict: BOUNDED, general-`v` TRUE. No wall, no new infra.** Decorrelated first-principles +
Codex xhigh (artefact: `codex/hindep-scope-{prompt,answer}.md`). This is the verify-first gate on the
one adjudication gating the last DLN-specific D1 piece (the concrete selected-minor chart).

## Why this is the irreducible core

The §SEL route reduced D1's `≥`-leg to `{concrete Φ + invertible f' + germ}`, and `f'` invertible ⟺
the `nReg` selected gradients `∇g_S(v)` are linearly independent (`f'`'s top block) = **H_indep**. It
was always the carried hypothesis, never verified-first as bounded. So scoping it before the
multi-tide concrete build was mandatory.

## Q1 — H_indep BOUNDED (the rank computation)

`dlnLoss H B A = ∑_{ij} g_ij(A)²`, `g_ij = (prod A − B)_ij`, L = 2 (`prod A = A¹·A²`). At an optimal
`v`: `prod v = B`, `rank B = r`. The gradient `∇g_ij(v)` acts on `(δ¹, δ²)` by
`(δ¹ A²_v + A¹_v δ²)_ij`. So `im Dg(v) = {δ¹ A²_v + A¹_v δ²} ⊆ Mat_{H0×H2}`, and with `p = rk A¹_v`,
`q = rk A²_v`:

    dim im Dg(v) = H0·q + p·H2 − p·q       (the intersection {δ¹A²} ∩ {A¹δ²} = A¹·Mat·A², dim p·q)

Writing `p = r + a`, `q = r + b` (both `≥ r` since `prod = A¹A²` has rank `r`):

    nReg_v − nReg = (p−r)(H2−q) + (q−r)(H0−r) ≥ 0,    nReg := r(H0+H2−r).

So **`rank Dg(v) = nReg_v ≥ nReg` at EVERY optimal `v`** — an independent `nReg`-subset of
`{∇g_ij(v)}` always exists ⟹ H_indep holds general-`v`, not deepest-only.

**Caveat (Codex):** the "`> nReg` at a middle stratum" is only strict under the displayed conditions;
equality can recur if the extra rank is invisible at an endpoint bottleneck. Immaterial — `≥ nReg`
always holds, which is all H_indep needs.

**Lean route (BOUNDED), no determinantal-tangent / Gauss-Newton infra:**
1. `prodAuxEntryDeriv` (banked, `DeepestRegSliceFderiv`) identifies the derivative rows with the
   `∇g_ij`.
2. a finite-dim linear-algebra lemma `finrank (range (fun (δ¹,δ²) => δ¹·A²_v + A¹_v·δ²)) ≥ nReg`
   (or the `≥` consequence directly).
3. `exists_linearIndependent'` (Mathlib) to extract the `nReg`-subfamily — the pattern already used
   in `RankLocusClosed.lean`.

## ★ The load-bearing refinement (operator-relevant)

**H_indep BOUNDED does NOT build the full chart.** H_indep gives only `f'` invertible (the chart
*exists*). The genuine remaining D1-at-general-`v` content is the **post-chart residual FORM**:
`F = ∑_{k∈S} s_k² + ∑_{α∉S} q_α²` (the selected coords become `s`, the rest become the residual `q`)
together with the germ `lossFlatShift =ᶠ F∘Φ` near the basepoint. That is the analytic
chart/splitting obligation — the residual D1 gap is the germ/residual-form identification, NOT H_indep.

## Q2 — the chart is needed pointwise

`deepest_le_of_optimal_of_iftResidual` consumes `hchart` at the given `v`; since H_indep holds
everywhere there is no bad-gradient locus to avoid. The only theoretical lightener — a crude rank-only
lower bound where `(nReg_v − nReg)/2 ≥ coreDeepest` (there `rlctAt v ≥ nReg_v/2` already gives the
inequality) — still needs a smooth-rank/submersion lower bound, so it is not actually lighter. The
chart-sensitive locus (needs the full chart + residual analysis) is `(nReg_v − nReg)/2 < coreDeepest`,
including all tight `nReg_v = nReg` points when `coreDeepest > 0`.

## Build plan (entry-wise — per the `Params H`-not-normed finding)

`Params H` carries no `NormedAddCommGroup`/`NormedSpace` instance, so smoothness cannot route through a
`ContDiff` map into `Params H`; everything goes entry-wise into `ℝ` (as `DeepestFramedProduct` does).

0. `paramsEquivFlat_symm_entry` — `((paramsEquivFlat H).symm x) s i j = x (flatIndexOf s i j)` (the
   flatten-symm is a reindex; each `Params`-entry is one flat coordinate). The unblocker.
1. `contDiff_lossFlatShift` — entry-wise via `contDiff_prod_entry` + the coordinate lemma +
   `contDiff_apply` on the normed `Fin N → ℝ`.
2. H_indep — the Q1 rank lemma + `exists_linearIndependent'`.
3. concrete `Φ` = `(g_S − g_S(v), complement P)`, `f'` = block `(∇g_S ; P)` invertible
   (`LinearEquiv.toContinuousLinearEquiv`), `ContDiff ℝ 2` (polynomial).
4. the germ `lossFlatShift =ᶠ F∘Φ` from the on-image identity `g_k∘Ψ.symm = s_k`.
5. the `(Fin N → ℝ) ≅ (Fin nReg → ℝ) × Y` MP reindex; wire `dln_hchart_flat` → the slot
   (`deepest_le_of_optimal_of_iftResidual`'s `hchart`).

Banked supporting chain (all clean-three `[propext, Classical.choice, Quot.sound]`):
`S1ChartTransfer.rlctAtOn_eq_of_boundedUnit_chart`, `S1IFTChart.{exists_boundedUnit_chart_of_contDiffAt,
rlctAtOn_eq_of_contDiff_chart}`, `D1HChartFlatten.{rlctAt_eq_rlctAtOn_lossFlatShift, dln_hchart_flat}`.
