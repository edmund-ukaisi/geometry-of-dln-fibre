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
| 07 | formalisation (tide) | **S4b — `SchurLoc`-linear (over-base) trivialization** `chartDsigAt_schurLocTensorEquiv` + `chartDsigAt_flat_over_schurLoc` (chartwise fibre-family flatness over the base) | **landed** · completes S3+S4 chartwise |
| 08 | review (hardener) | batched bedrock pass on the bundle story (S2c, S3, S4, S4b) | pending (convene post-merge) |

Parked (roadmap): S2b — conormal `I/I²` free of rank `= codim` (RLCT-relevant dual of S2; confirmed
REAL-BUILD by hardener); S5 — reusable `IsLocallyTrivialProduct` API (packages S4/S4b); S1 in-file
non-vacuity `example` (bedrock-2.1 nicety); R1 — `targetOverlapTransition` overlap-gluing (needed for a
single GLOBAL `Flat π`/`FiberBundle` morphism over all `rankROpen`, beyond the chartwise S4b).
