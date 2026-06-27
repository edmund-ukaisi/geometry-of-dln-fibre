# Threads — `fibration-geometry`

Index: status / type / one-line subject. `open` / `in-progress` / `blocked` / `review-pending` /
`closed` / `abandoned`. Per-thread notes in `threads/<NN>-<slug>/thread.md`.

| NN | type | subject | status |
|----|------|---------|--------|
| 01 | formalisation (tide) | S1 — rank bridge `P ∈ rankROpen ↔ rank over κ(P) = r` → set-of-primes `rankROpen = {rank=r}` | landed · hardener-pending |
| 02 | formalisation (tide) | S2 — smooth-block (Kähler `Ω` free, `rank(Ω)+codim=ambient`) | landed · hardener-pending |
| 03 | formalisation (tide) | S3 — flatness payoff (`Flat π` over `rankROpen` + universally-open + `rankAtStalk`) | in-progress |
| 04 | formalisation (tide) | S4 — honest `locallyTrivial` over `rankROpen` (promote the atlas via S1) | in-progress |
| 05 | review (hardener) | decorrelated bedrock pass on S1 + S2 (`@ 3cb4fc17`) | closed · **both PASS-WITH-NOTES, bedrock, no CRITICAL** |
| 06 | formalisation (tide) | S2c — `TopDimMinPrimes(sweepFibreRing)` nonempty under the kostant gate → closed `exists_smoothBlock_certificate` | in-progress |

Parked (next wave / roadmap): S2b — conormal `I/I²` free of rank `= codim` (RLCT-relevant dual of S2;
confirmed REAL-BUILD by hardener, not Just-Do-It); S5 — reusable `IsLocallyTrivialProduct` API
(packages S3+S4); S1 in-file non-vacuity `example` (bedrock-2.1 nicety, ~half-day — roadmap).
