# R1-RESIDUAL MAP — the EXACT residual of `resolution_charts` (the convergent bottleneck)

Read-only scope (genm-p44c worktree; NO .lean writes). `resolution_charts` (Skeleton:1228) is the R1
rung: `rlctAtOn(dlnLoss M 0) 0 = ⨅ᵢ monomialThreshold (d i)(k i)(h i)` for a chart family `(ι,d,k,h)`,
`hMid : ∀ s, 0 < M s`. It gates 3 of 5 rungs (L2 via #44/hcore, R1 itself, D1 ≥-leg). Verdict: the VALUE
is BANKED; the residual is TWO analytic cover atoms, BOTH reduced M-agnostically (sorry-free) to ONE
per-M chart construction each — BOUNDED (no fresh wall beyond #120), but real geometric work.

## (a) What's BANKED toward it

| Piece | Status | What it gives |
|---|---|---|
| `routeLayerAtlas` (RouteMLayerSplit) | **0 sorry** | the chart family `(ι,d,k,h)` in `resolution_charts`'s exact tuple shape (layer-collapsing atlas) |
| `routeLayerAtlas_value_eq_lambdaCore` (RouteMLayerValue) | **sorry-free mod S2** | **the VALUE: `⨅ monomialThreshold = ofReal(lambdaCore M)`** — A1 (`lambdaCore_eq_clean` + S2 `monomial_rlct`). The `rlctAtOn = ⨅` content's RHS is DONE. |
| `routeMLayerCover_of_atoms` (RouteMLayerCover) | **sorry-free ASSEMBLY** | reduces `IsRouteMCover` to its 2 analytic atoms; the 3 structural fields (`Fmeas`/`Uopen`/`Umem`) + `cover_le` RHS-positivity proven general-M |
| `routeMBoxThresholdFinite_rrp` / `schurRecStep_p` (R1-UPPER) | banked (r,r,p) | per-summand finiteness via recStep pivot-blowup — the `cover_le` per-leaf piece for (r,r,p) |
| smeared L2 square / `RouteMSmearedAchieverGeneral` | 0 sorry | per-family achiever-chart bedrock for the LOWER leg |
| 2 anchors `(4,4,2,2)`, `(3,3,4)` `NodeAchieverChart` | **sorry-free** | both ends of the family — the LOWER atom built concretely |
| genm-detfderiv `|det Dφ| = u_p^{minAdm−1}·spectator` | **IN-FLIGHT (detfderiv's lane — REFERENCE only)** | the chart Jacobian the LOWER atom's per-M construction rides on (#77/#80) |

## (b) The ASSEMBLY path (how it composes)

`resolution_charts` = `resolution_charts_of_layerCover` (sorry-free) applied to **`IsRouteMCover` over the
layer family**. `IsRouteMCover` (5 fields) = `routeMLayerCover_of_atoms` (sorry-free) of {3 structural
(done) + `cover_le` RHS-pos (done) + **2 residual atoms**}. The VALUE `⨅ = lambdaCore` is the SEPARATE
banked lane (A1). So: **value DONE; the equality's `rlctAtOn = ⨅` content = the 2 cover atoms.**

## (c) The GENUINE RESIDUAL = 2 analytic cover atoms (both M-agnostically reduced to one per-M chart)

1. **`cover_ge_div` (LOWER / box-integral divergence, R1.6) — the CLEANER leg.**
   `∫⁻_{[−ε,ε]^N} |routeMCore M|^{−c'} = ⊤` at `c' = ½·minAdm M`, along the **achiever leaf ONLY** (one
   diverging leaf suffices ⟹ immune to the corank-≥2 obstruction). Reduced M-agnostically + sorry-free
   (`routeMCore_box_diverges_of_nodeChart`, NodeAchieverChart.lean) to "construct one `NodeAchieverChart M`":
   a chart `φ: box→flat`, `|det Dφ| = u_p^{minAdm−1}·spectator`, `routeMCore∘φ = u_p²·V` (V bounded +
   a.e.-pos) ⟹ `∫ ≥ ∫ u_p^{(minAdm−1)−2c'} = ⊤` at exponent −1. **BANKED:** 2 anchors; the chart Jacobian
   identity is genm-detfderiv's in-flight lane (#77/#80 — REFERENCE, don't enter). Honest note in-repo:
   an OLD "not reachable" verdict (2026-06-24) is SUPERSEDED — "the chart route, not the squeeze, is the
   path." (The squeeze gives only `rlctAtOn ≤ ½minAdm`, strictly weaker than boundary divergence; filling
   `=⊤` from the point bound would be the forbidden value-correct/germ-degenerate trap.)
   **BOUNDED.** Open content = the per-M `NodeAchieverChart` construction (= detfderiv's |det Dφ| + the
   `routeMCore∘φ` collapse), assembled ∀M (#80). Watch: the ∀M chart family construction is the multi-tide.

2. **`cover_le` (UPPER / below-threshold finiteness) — the HARDER leg.** Two sub-obstructions:
   (a) per-summand finiteness — banked for (r,r,p) via recStep; (b) **COMPLETENESS** — the recursively-
   generated pivot charts COVER `(−1,1)^N` up to null ("no missing strata" combinatorial cover);
   iterating recStep does NOT package this. **BOUNDED-but-harder**: the completeness/measurable-cover is
   the genuine open transcription (no machine counterexample; it's a packaging/induction gap, not a
   false statement). This is the heavier of the two.

## (d) BOUNDED-vs-WALL per piece + the codim-bypass question

- VALUE (`⨅ = lambdaCore`): **DONE** (mod the cited S2 axiom).
- `cover_ge_div` (LOWER): **BOUNDED**, 2 anchors + M-agnostic reduction; per-M chart = detfderiv's lane.
- `cover_le` (UPPER): **BOUNDED-harder** — the measurable-cover COMPLETENESS is the real open piece (a
  combinatorial/induction transcription, not a wall). No false statement; no counterexample.
- **None is a fresh research wall beyond the named #120** (L≥3 grouped diffeo). All L=2 / ∀M-at-L=2.
- **Codim-bypass (½·min_strata codim, no explicit Jacobians)?** NOT instantiated — grep finds no codim
  architecture in the codebase, and the in-repo note is explicit that "the chart route, NOT the squeeze,
  is the path." A codim route would only bound the RLCT ABOVE (smooth-locus codim) — the DIVERGENCE
  (lower) leg `=⊤` at the sharp `c'=½minAdm` genuinely needs the chart Jacobian's exponent −1 (a codim
  upper bound cannot produce the boundary `∫u^{−1}=⊤`). So codim does NOT bypass the LOWER leg; it could
  only help the UPPER (finiteness ≈ smooth-locus codim ≥ minAdm), but that's the leg that's NOT the
  bottleneck. Verdict: the chart-Jacobian architecture is load-bearing for the LOWER leg; no clean codim
  bypass of the convergent bottleneck.

## Bottom line for routing

R1's value is DONE; R1's residual = the analytic CHART COVER, decomposed sorry-free to TWO per-M chart
atoms: the LOWER (divergence, cleaner, 2 anchors, rides detfderiv's |det Dφ|, assembled ∀M = #80) and
the UPPER (finiteness + the measurable-COMPLETENESS packaging). Both BOUNDED; the LOWER is the
load-bearing convergent piece (gates hcore → #44/L2/D1). The ∀M `NodeAchieverChart` (#80, on detfderiv's
Jacobian) is the single highest-leverage build — closing it lands `cover_ge_div`, which with the UPPER
completeness closes R1's `rlctAtOn = ⨅`, which ▸ the banked VALUE gives hcore = lambdaCore, cascading to
3 rungs. So: route the ∀M NodeAchieverChart (LOWER) as the lynchpin build; it depends on detfderiv's
in-flight |det Dφ| (coordinate, don't double-drive). The eIn/eOut interior-det tide IS that |det Dφ| —
so it's CHARGE (it's the bottleneck's dependency), not defer.

Read-only; no .lean writes. Refs: Skeleton:1228, RouteMLayerValue/RouteMLayerCover(GE)/NodeAchieverChart,
genm-detfderiv (#77/#80, REFERENCED not entered).
