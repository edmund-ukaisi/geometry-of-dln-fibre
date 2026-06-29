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
