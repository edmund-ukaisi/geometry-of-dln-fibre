# Synthesis — `foundation-lift` (foundation-lift II)

*Accumulates as rungs/phases land. Opening shape: [`brief.md`](brief.md) + [`priorities.md`](priorities.md).*

The second **build-the-buildable** expedition: lift three more batches of project-local-but-general
`DLNFibre.Core` modules to Mathlib-grade, in phases — **P1** components & local dimension (`TopDimMinPrimes*`
+ localization no-drop), **P2** determinantal & elimination algebra (graph ideals + matrix-rank), **P3**
smooth/cotangent (`CotangentJacobian`) — each its own PR, driven autonomously on stacked branches off
`origin/dev` `00fb7238` (PR #14). Built on #14's dimension stack; same machine + lessons L1–L4.

## Tick log
- **2026-06-29 — kickoff.** Coverage recon closed (corrected the audit: P1 = `TopDimMinPrimes*` not
  `SigmaComponents`/`ThetaComponentCount`; P3 one module; `SmoothPointRegular`/`NoetherMonicPositioning`/
  `rank_map_eq_of_injective`/`minimalPrimes` already done in #14). Worktree on `expedition/foundation-lift-p1`
  off `origin/dev`, build warmed (430M, trees identical). Scaffold + cron set. P1-R1 dispatched.
- **2026-06-29 — P1-R1 LANDED** (`2ab2995a`). The minimal-primes SPIKE re-homed to
  `Core/MinimalPrime/Finite.lean`: `Ideal.minimalPrimes_sInf_of_finite_of_isPrime` (minimal primes of a
  finite prime-family `sInf` = inclusion-minimal members), with a bonus hypothesis-weakening
  `[CommRing]→[CommSemiring]` (build-confirmed). Sibling-clash cleared, re-gate green 3820, axiom-clean,
  L3-clean. Review **waived** (low-risk warm-up — review reserved for the three crux rungs). → P1-R2 dispatched
  (localization `≤`-half).
