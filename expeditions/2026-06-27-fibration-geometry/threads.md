# Threads — `fibration-geometry`

Index: status / type / one-line subject. `open` / `in-progress` / `blocked` / `review-pending` /
`closed` / `abandoned`. Per-thread notes in `threads/<NN>-<slug>/thread.md`.

| NN | type | subject | status |
|----|------|---------|--------|
| 01 | formalisation (tide) | S1 — rank bridge `P ∈ rankROpen ↔ rank over κ(P) = r` → set-of-primes `rankROpen = {rank=r}` | landed · hardener-pending |
| 02 | formalisation (tide) | S2 — smooth-block (Kähler `Ω` free, `rank(Ω)+codim=ambient`) | landed · hardener-pending |
| 03 | formalisation (tide) | S3 — flatness facts (localization + SchurLoc-free model + scheme `UniversallyOpen`); cheap-flatness verdict settled | landed (partial) · payoff gated on S4b |
| 04 | formalisation (tide) | S4 — honest per-chart local PRODUCT over `rankROpen` (`RankROpenPerPivotLocalProduct`; k-algebra, uncocycled) | landed · fidelity PASS |
| 05 | review (hardener) | decorrelated bedrock pass on S1 + S2 (`@ 3cb4fc17`) | closed · **both PASS-WITH-NOTES, bedrock, no CRITICAL** |
| 06 | formalisation (tide) | S2c — `TopDimMinPrimes` nonempty → `exists_topComponent_smoothBlock_certificate` (hypothesis-free) | landed · **closes S2 Deferred (c)** |
| 07 | formalisation (tide) | **S4b — `SchurLoc`-linear (over-base) trivialization** `chartDsigAt_schurLocTensorEquiv` + `chartDsigAt_flat_over_schurLoc` (chartwise flatness over **SchurLoc**) | **landed** · hardener PASS (non-circular); completes S4 over-base; flatness over SchurLoc (NOT literal `rankROpen` — P-bridge + R1) |
| 08 | review (hardener) | batched bedrock pass on the bundle story (S2c, S3, S4, S4b) `@ caa96288` | closed · **all PASS / PASS-WITH-NOTES, no CRITICAL**; S4b non-circular (2 ways + Codex); global-flatness-without-R1 = NO (needs P-bridge) |
| 09 | formalisation (tide) | S5 — capstone `RankROpenOverBaseLocalProduct` + `reducedFibre_existsOverBaseProductChartAt_rankEq` (over-base product + flatness over SchurLoc, base distinction + open items carried) | **landed** · reviewer PASS · precision-check PASS |

Parked (roadmap): **P-bridge — chart-base identification** `SchurLoc ≅ sweepSigmaRing|basicOpen(chartDsigAt)`
(+ structure-map compat) — turns S4b's flatness-over-SchurLoc into genuine flatness over `rankROpen`;
real build, AHEAD of R1; **R1** — `targetOverlapTransition` overlap-gluing (single GLOBAL
`Flat π`/`FiberBundle` morphism over all `rankROpen`, after P-bridge); S2b — conormal `I/I²` free of
rank `= codim` (RLCT-relevant dual of S2; REAL-BUILD per hardener); S1 in-file non-vacuity `example`
(bedrock-2.1 nicety); singular-locus split (R2, RLCT-runway lower bound — next expedition).
