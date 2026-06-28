# R1-LOWER general leg — SPEC-FIRST wall-check (genm-nodechart, #80)

**Seat:** formaliser (tide). **Date:** 2026-06-28. **Gate:** the lone `sorry`
`routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE.lean:133`). **Method:** read the
NodeAchieverChart bundle + assembly + ALL four anchors + the banked telescope/det/rate machinery +
the boundary-class trichotomy + the genM design certificates (threads 32 / 36) + one decorrelated
xhigh Codex (`codex/wallcheck-{prompt,answer}.md`).

## VERDICT (one line)

**The commissioned target — "construct ONE `NodeAchieverChart M` ∀M" — is the WRONG target, and the
leg is ALREADY being built by OTHER tides (`aoyagi-det`, `fm3 #99`) as a 4-way case split across
files OUTSIDE my named scope.** It is NOT a single research wall and NOT a single chart; it is a
4-way single-pivot case split, ~80% built, with THREE residuals (one likely-genuine interface gap,
one unproven structural lemma, one heavy build). **STOP-and-report, do not build** (spec-first gate +
Item-61 collision-avoidance). Codex (decorrelated, xhigh) independently agrees the single-multi-axis
framing is wrong and the 4-way split is right.

## Why a single `NodeAchieverChart M` ∀M is the wrong target

`NodeAchieverChart M` pins `leafH p = minAdm−1` on the binding axis, but the chart Jacobian
`|det Dφ| = ∏_j |u_j|^{leafH j}` is **construction-sensitive** (thread-32 §2, validated exact): the
spectator-axis exponents have no clean closed formula across the family —
- `(4,4,2,2)`: pure radial, ONE weighted axis, `|u0|^3`.
- `(3,3,3,3)`: FOUR weighted axes, `|u0|^5·|u1|^4·|u4|^2·|u9|^3` (spectator exps 4,2,3 from the
  LDU/Schur/coupling block structure of the `phiGen`/Frame chart).
There is no uniform multi-axis `leafH` formula, so a single uniform `phiGen`-based chart's det cannot
be stated ∀M without the construction-dependent exponent vector. The resolution (cert
`certificate-genM-smeared.md`, retracting the multi-axis concern): use a DIFFERENT construction per
branch, each **single-pivot** (`leafH = minAdm−1 at p, 0 elsewhere`).

## The actual general construction = a 4-way case split (the right target)

`routeMCore_box_diverges_achiever M` ∀M is assembled by case-splitting M's descent structure
(`RouteMBoundaryClass.lean` — the `aoyagi-det` tide's classifier):

| branch | guard | chart | Lean status |
|---|---|---|---|
| L=1 | `L = 0`-ambient | `DeepestBaseL1` pure radial | banked |
| INTERIOR | `InteriorDrop M` (interior boundary drops both row+col rank) | colPath Schur, single-pivot | witness+`Ubound` DONE sorry-free (`RouteMAchieverWitnessInterior`); **chart cov/det residual** |
| BOUNDARY-CLEAN | `¬InteriorDrop ∧ deepRank = deepRows` | whole-deepest radial | **DONE sorry-free** (`cleanNodeChart M` → `routeMCore_box_diverges_clean`, `RouteMBoundaryCleanChartFull`) |
| BOUNDARY-SMEARED | `¬InteriorDrop ∧ deepRank < deepRows` | rational single-pivot `φ_sm` | instances (1,2,1)/(1,3,2)/(2,3,1) DONE; **∀M rational `cov` residual** |

The RATE `routeMCore (phi u) = u_p²·U` is **banked ∀M** (`routeMCore_phiFlatStructV` /
`routeMCore_phiGen`, single radial pivot). The det-telescope ENGINE (`composeFold_abs_det_leafH`) is
banked. A generic divergence route `routeMCore_box_diverges_of_RadialMPChart` (ψ MP-embedding + R
radial) bypasses `NodeAchieverChart` for the rational branch.

## The THREE residuals (ranked) — the precise wall

1. **EXHAUSTIVENESS GATE — `deepRank M ≤ deepRows M` ∀M (the achiever-path bottleneck `r ≤ m1`).**
   The trichotomy totality `interiorDrop_or_boundaryClean_or_boundarySmeared`
   (`RouteMBoundaryClass:120`) is PROVEN but carries `hle : deepRank M ≤ deepRows M` as a
   **hypothesis** — validated numerically (46/46 + 20/20) but **NOT proven in Lean** (`deepRank`,
   `deepRows` are noncomputable `Classical.choose` argmin widths, so not `decide`-reducible). This is
   the coverage risk Codex flagged most strongly. Until it is proven, the 4-way wiring is incomplete
   — there could be no uncovered class, but the split is not provably total. **Bounded math
   (monotone-`Text`-along-achiever-path argument), NOT obviously a wall, but unproven.**

2. **SMEARED-branch rational `cov` — likely a genuine interface gap.** `φ_sm` divides by a Gram minor
   `(P_1ᵀP_1)⁻¹` (rational, undefined on a null pole). The polynomial `pivotBlowupOn` `cov` the
   banked charts use does NOT apply; it needs the a.e.-analytic transport `weightedThreshold_transport`
   (S1, banked) — whose hypotheses (proper a.e.-analytic off a null set, the Jacobian-weight form)
   are flagged as **un-confirmed for this specific rational-pole map** (cert §6 caveat). Codex: the
   main DESIGN risk — "the smeared cov API if it cannot express 'valid off a null rational pole.'"

3. **INTERIOR-branch chart cov/det — the heaviest remaining BUILD (bounded, not a wall).** The
   witness/`Ubound` are DONE; the chart `cov` (Jacobian c-o-v, `injOn` off the weighted-axis planes,
   `|det Dφ| = |u_p|^{minAdm−1}`) is the large Lean build that remains. Bounded engineering.

## SCOPE / COLLISION (the load-bearing operational finding)

The general construction lives in files NOT in my commissioned scope and is actively owned by other
tides (recent commits): `aoyagi-det` (`RouteMBoundaryClass`, `RouteMBoundaryCleanChartFull`,
`RouteMAchieverWitnessInterior` — INTERIOR/CLEAN/classifier, "WALL 2") and `fm3 #99`
(`RouteMGeneralAssembly`). My named scope (NodeAchieverChart / RouteMLayerCoverGE* / RouteMAchiever* /
RouteMGenFlatChart / RouteMFlatStructV / RouteM4422 / RouteM3333* / RouteM121Smeared) is the
SUBSTRATE the 4-way split consumes, but the WIRING + the open branches sit elsewhere. Building a
competing `nodeChartGeneral` here would **collide** (Item 61 strict). The commission's premise ("one
sorry closes the whole leg via one chart, the substrate is heavily banked") is outdated — the leg is
a multi-file 4-way assembly already in flight.

## Recommendation to the controller

Do not have me build a single `NodeAchieverChart M`. Instead, the controller should decide whether to
(a) reassign me a SINGLE non-colliding residual within the 4-way split (e.g. PROVE the exhaustiveness
bottleneck `deepRank ≤ deepRows` ∀M — residual #1, self-contained, in `RouteMBoundaryClass` which is
small; or confirm the `weightedThreshold_transport` interface on `(1,2,1)` per Codex's cheapest
test — residual #2), or (b) coordinate the 4-way wiring with the `aoyagi-det` / `fm3` owners. The
honest leg-closing path = residuals #1 + #2 + #3, not "one chart."
