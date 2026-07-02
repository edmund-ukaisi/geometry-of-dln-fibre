# Threads — `rlct-foundation`

Per-rung formaliser/reviewer/scout threads (ladder in [`priorities.md`](priorities.md)). One
**builder/committer** per shared worktree at a time; read-only auditors alongside. Controller integrates +
re-gates per [`loop-prompt.md`](loop-prompt.md). Branch `expedition/rlct-foundation` (off `dev` `10edbdc3`).

## Status

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| R1 | build (SWE) | — | ⏳ NEXT (crux) | citation cordon: `@[cited]` attr + `collectAxioms` accounting core + `#audit_cited` + `scripts/cited` gate + adversarial tests + `docs/policies/citation-cordon.md`; retrofit `RlctRealInterface`. **Battle-test.** Decorrelated review. |
| R0 | scout | — | ⏳ (parallel) | Mathlib analytic-coverage recon + build-vs-cite reach (kill-questions in brief). |
| G1 | formaliser | — | ⏳ (parallel) | non-monotone fibre `θ` — component-count fibration transfer + rank-locus corollary. No new math. |
| R2–R8 | — | — | ⛔ blocked on R1+R0 | the RLCT foundation + payoff rewire. |

## Concurrency rule (this expedition)
At most one builder/committer in `.claude/worktrees/rlct` at a time (a second `lake build` corrupts `.lake`;
two `git commit`s race the index). Read-only auditors may run alongside one builder. Rungs on the same file
serialize. R1 (tooling/`scripts`), R0 (read-only recon), and G1 (geometry, disjoint files) can be dispatched
concurrently *only* if they touch disjoint paths + one builder rule holds — otherwise serialize.

_Updated each tick._
