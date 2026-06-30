# Thread: D1 second-peel `extraCount` chart producer (L = 2)

Tide: build the one genuine open analytic piece of the L = 2 D1 `≥`-leg — the SECOND-peel
`extraCount` interface chart on the first-peel slice residual.

## VERIFY-FIRST GATE VERDICT: BOUNDED (not #120-wall-entangled)

The second peel reuses the SAME bounded selected-minor IFT technique as the FIRST peel
(`dln_hchart_residual`); it does NOT route through `DeepestGaugeChart`'s open #120 gauge-slice
sorry. The `DeepestGaugeChart` (rank-`r`-exact pivots, grouped inter-layer diffeo AT THE DEEPEST
POINT) feeds the SEPARATE deepest-side gate #44 (`hDeepest`), not my `v`-side target `hchart₂`.

**Decisive crux (decorrelated Codex xhigh, `codex/gate-{prompt,answer}.md`):** the SCALAR gradient
`∇R(t0)` of the first-peel slice residual `R = ‖h‖²` VANISHES (since `h(t0) = 0`), so a
selected-minor IFT on the scalar `R` is impossible. BUT the `extra` Morse block of `R` is exactly
FIRST-ORDER rank in `dh(t0)` (`Hess R(t0) = 2·(dh(t0))ᵀ·dh(t0)`). So the bounded route selects the
minor from the residual VECTOR `h = q(0,·)` (a Jacobian-rank condition on the vector), EXACTLY as the
first peel selected its minor from the loss-entry vector `g_{ij}`, not from the scalar loss `∑ g²`.
The `extra` directions being Morse (Hessian) in `R` but first-order in the vector `h` is the load-
bearing observation; it is what keeps the second peel at the bounded IFT altitude, off the #120 wall.

## What landed (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

`lean/DLNFibre/DLN/RLCT/Validate/D1SecondPeelChart.lean` (670 LoC):
- `secondPeel_hchart_residual` — the abstract, NETWORK-FREE second-peel `hchart₂` producer. For a
  `C²` residual vector `h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)` with `h t0 = 0` and an invertible
  `extra × extra` Jacobian minor at `t0`, charts `R = ∑ h i²` into `∑ s² + ‖q₂‖²` on `ℝ^extra ×
  ℝ^(N−extra)` for a GLOBAL `C¹` residual `q₂`. The structural ANALOG of `dln_hchart_residual`.
- `secondPeel_hchart_residual_zero` — the centered (`g 0 = 0`) case; the heavy spine.
- The abstract chart machinery (mirroring the D1HChart* template, network-free): `abChartΦ` (+ sel/
  compl/zero), `dAbChartΦ`/`dAbChartΦmat`/`abChartFDerivEquiv` (+ `det ≠ 0` block-triangular),
  `contDiff_abChartΦ`, `abSplitHomeo` (the MP reindex `ℝ^N ≃ₜ ℝ^extra × ℝ^(N−extra)`), `abGermA`
  (the germ split), `abRawResidVec`.
- A slot-check `example` confirming the producer feeds `deepest_le_of_optimal_of_iftResidual`'s
  `hchart₂` hypothesis shape (durable interface contract).

`lean/DLNFibre/DLN/RLCT/Validate/D1SecondPeelAssembly.lean` (95 LoC):
- `deepest_le_of_optimal_secondPeel_discharged` — the L = 2 D1 per-point `≥`-leg with the SECOND
  peel DISCHARGED (built from data, no longer hypothesized). Wires the producer + the two-peel
  `deepest_le_of_optimal_of_iftResidual` + #44 (`hDeepest`) + the R1 interface (`hInterface`,
  supplying both the degraded-core value `ofReal(lambdaCore M')` and the second-peel slice
  non-vanishing). The first-peel chart `hchart`, `hDeepest` (#44), `hInterface` (R1) are EXPLICIT
  named-open hypotheses; the second peel is the new closed content.

## Named-open gates (none silently assumed)

- FIRST-peel chart transfer `hchart` (DLN-specific bounded-unit IFT at `v`; `dln_hchart_residual`).
- `hDeepest` = #44 (`deepest_regular_core_normal_form_of`, ready given R1 core value + `hGne`).
- `hInterface` = the R1-resolution value at `M'` + the degraded-core non-vanishing (`hR₂ne`-shape).
- The SECOND-peel selected-minor non-degeneracy `hminor₂` (Jacobian-rank on the residual vector).

## Method note

Pre-translation to center `0`: the producer at general `t0` wraps the centered lemma via the
translation homeomorph `Homeomorph.addRight t0` (`rlctAtOn_comp_homeomorph`, MP) + the chain rule
`fderiv_comp_add_right` for the minor transport. The centered lemma is the verbatim spine of
`dln_hchart_residual` with the DLN loss entries replaced by the abstract residual-vector components.

Build: `scripts/lb DLNFibre.DLN.RLCT.Validate.D1SecondPeelAssembly` — green. Not in the aggregator
(`DLNFibre.lean`) — controller wires.
