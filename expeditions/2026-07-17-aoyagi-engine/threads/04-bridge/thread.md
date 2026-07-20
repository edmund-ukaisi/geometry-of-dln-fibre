# Thread 04 — bridge (t04-bridge, pen-and-paper, lane 2)

Owns the **chart↔monomial-integrand CoV bridge** (r2 finding 2): the missing structure that makes
`region_glue` (`Engine/EngineObligations.lean:166`) a placeholder. Design-first; gates the region-glue
tide. NO Lean built. Exact algebra (sympy) + one decorrelated Codex consult.

## Deliverable

`cert-bridge-design.md` — the corrected structure + the **signature diff** + the **CanonicalResolution
bundle change (flagged loudly)**.

## The bug and the fix, in one paragraph

`region_glue`'s `ChartsCover` constrains the leaf `chartDom` only as an abstract `Set`; nothing ties it
to a chart MAP or the loss, so `chartDom = univ` (`witLeaf`) satisfies it vacuously and the current
signature has an exact counterexample (`g-chartscover-vacuity.py`: fake all-`univ` atlas, `divExp={4}`,
`c'=8/5 ∈ [3/2,2)` → hyps hold, box diverges). The fix: a per-leaf CoV bridge — a `chartMap`
`φ_l : srcBox → Params M` with (P) a loss-pullback `F∘φ_l = (∏ u_k²)·R_l` (`R_l` bounded-unit OR Morse
rank `resRank`) and (J) a Jacobian ledger `|det Dφ_l| = (∏ u_k^{divExp_k−1})·const`, plus a strengthened
**image cover** (`⋃ φ_l '' srcBox`, not abstract `chartDom`). This ties `chartDom` to the true monomial
exponents; `witLeaf(univ)` then fails to type-check as canonical (vacuity closed at type strength).

## Exact verification (sympy, all exit 0)

| chart | pullback | Jacobian | residual | threshold |
|---|---|---|---|---|
| (2,2,2) δ-chart | `α²δ²·R` | `α³δ²` | Morse rank 5 | 3/2 = ½minAdm (BINDING) |
| (2,2,2) u-chart | `α²u²·R` | `α³u²` | bounded unit | 3/2 (BINDING) |
| (3,3,4) corank-2 | `δ²·R`, δ **shared** over all 8 gens | `δ³` | Morse rank 8 | 2 = ½minAdm(2,2,4) |

## Two findings for the tide

- **F1** the leaf integrand is monomial × RESIDUAL (Morse rank `resRank` or bounded unit), NOT a pure
  monomial — the current `monomialChartIntegral` omits `R_l`; the residual ratio `resRank/2` must enter
  the min (recommend: fold `resRank` into `terminalExponents`; pins `resRank ≥ minAdm`).
- **F2** at corank ≥ 2 a single divisor divides EVERY generator (the sharing) — carried by the typed
  `support` field (compass fork-3).

## P8 composer interface pinned

The one genuine GAP: the elementary blow-up box-level Jacobian CoV (monomial, non-unit Jacobian) + its
composition via Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (fed by `LeafJacobian`).
Shears are banked (`CoreShearMP`); the Morse/monomial reads are banked (`RouteMSJRadialInt/RadialPolar`);
the RLCT-level transport is banked (`S1NonMPTransport.weightedThreshold_transport`).

## Artifacts

- `battery-drafts/g-chart-bridge-pullback.py` (exit 0) — the 3-chart exact bridge verification.
- `battery-drafts/g-chartscover-vacuity.py` (exit 0) — the r2 bug made executable.
- `scripts/{bridge_verify,bridge_334_chart}.py` — the sympy computations.
- `codex/bridge-design-{prompt,answer}.md` — decorrelated consult (conclusion withheld).

## Open (for the controller / tide)

1. The bundle change (ChartsCover → ChartBridge in CanonicalResolution) is the controller's call —
   it re-opens the gated shape and adds content to `monomialization_terminates`.
2. `resRank ≥ minAdm` (residual never binds below ½minAdm) — a truth-witness obligation for the tide.
3. The P8 elementary-blow-up box-CoV — no banked lemma; the composer lane's core.
