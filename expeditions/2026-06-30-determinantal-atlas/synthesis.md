# Synthesis — `determinantal-atlas`

_Accumulates as rungs land. Final synthesis at close._

## Kickoff (2026-06-30)
Fourth **build-the-buildable** expedition, on `origin/dev` `a13b11f2` (after #14 dimension stack + FL-II + FL-III
orbit squeeze). Central question: build a Mathlib-grade, network-free `Core` library for **determinantal rank
geometry + the constructive pivot-chart atlas** (localization-overlap API → determinantal rank-stratum API →
per-pivot Schur trivializations + cocycle compatibility + a recon-gated bare `FiberBundle` capstone), and
re-express the DLN rank-locus wrappers as instances. Source: `/tmp/next_foundational_expedition_recommendation.md`
(Primary programme).

**Why (operator-confirmed):** consolidates the existing-but-scattered chart machinery (`dStratum`,
`productRankLocusLE`, `sigmaIdeal`, `RepCoord`, fragile double-localizations) into its honest, named,
**constructive**, reusable form — standard determinantal AG, the team's detail-at-scale strength. Core engine +
thin DLN adapter (the FL-III pattern). Foundation-cleanliness/bedrock, not a stuck headline.

**The constructive virtue:** the atlas is explicit + finite + computable — pivots indexed by (`r`-row, `r`-col)
subsets, charts `U_P = D(det A_P)`, trivializations the closed-form Schur `D = C A⁻¹ B`, transitions explicit
rational maps. Prefer constructive over abstract-existence throughout.

**The one discrimination (recon-gated):** the bare-`FiberBundle` capstone needs a **residue-field-rank bridge**
(charts cover every *scheme point*, not just `k`-rational ones). Likely detail-at-scale (basic-opens-cover +
minor↔rank over `κ(p)`), not a monument — recon confirms; build if so, else atlas+cocycle is the honest ceiling
+ roadmap the leap. The constructive atlas does not depend on the bare-bundle repackaging.

## Roadmap addition (this expedition)
The **RLCT generic-foundation programme** is written into [`ROADMAP.md`](../../ROADMAP.md) — the integrability-
threshold / zeta-pole RLCT definition, the generic invariance theorems, the normal-crossing certificate layer,
the quarantined citations, and the honest DLN payoff boundary. Tracked as the important next-after-this
programme; NOT built here (operator's scope call — clean scope over premature analysis).

## P0 — recon
_dispatched._

## Phase 1 / Phase 2
_pending the recon's refined ladder._
