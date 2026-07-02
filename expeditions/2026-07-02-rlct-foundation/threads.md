# Threads — `rlct-foundation`

Per-rung formaliser/reviewer/scout threads (ladder in [`priorities.md`](priorities.md)). One
**builder/committer** per shared worktree at a time; read-only auditors alongside. Controller integrates +
re-gates per [`loop-prompt.md`](loop-prompt.md). Branch `expedition/rlct-foundation` (off `dev` `10edbdc3`).

## Status

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| R1 | build (SWE/infra) | r1-cordon | ✅ **LANDED** `82c3b006` | citation cordon shipped + **controller-verified** (build 3836 green · gate `UNACCOUNTED=0 CITED=3 LOCATION=0` · sorries `0/3-axiom` · fixtures **13/13**). Parametric `@[cited]` + `collectAxioms` accounting (forget-proof) + `#audit_cited` + enforcing `scripts/cited` + 13 adversarial fixtures; retrofit `AoyagiCited.lean` (3 cites + proved interface + corner-0 payoff); `docs/policies/citation-cordon.md` graduated. Perf: `collectAxiomsBatch` (per-decl timed out >590 s → ~20 s). Aggregator-wired (controller). Codex-xhigh on design; reviewer `rev-cordon` auditing. |
| R0 | scout | r0-recon | ✅ **DONE** (recon delivered) | **GREENFIELD**: `rlctAt`/`rlctAtOn`/`weightedThreshold` are NOT on `dev` (cross-worktree only; ROADMAP §4b claim stale). Strong BUILD base (Mellin+`cpow` pole, `meromorphicOrderAt` arith, multidim CoV + integrability transport, rpow dichotomy, JapaneseBracket, parametric holomorphy); monuments confirmed absent (cite); coord-change invariance BUILDABLE. Value-vs-pole first-slice flag → operator. Codex CLI down (env). |
| G1 | formaliser | g1-fibre-theta | 🔄 building | recon calibrated the gap: the count chain is already `Monotone`-free up to `numTop d r` (only the cosmetic `numTop = cTheta` step needs it). Delivering the arbitrary-`d` `= numTop d r` floor + `..._of_rank` transport; closed-form corollary IF `numTop` perm-invariance is landed on-branch. Own worktree `rlct-g1`. |
| R2 | build | — | ⏳ ready — gated on **DEFINITION DECISION** (operator) | zeta-pole `(λ,m)` vs value-first-slice vs hybrid. R1 done ⟹ no longer R1-gated; awaiting operator's call (surfaced, non-blocking). |
| R3–R8 | — | — | ⛔ blocked on R2 | the RLCT foundation + payoff rewire. |

## Concurrency rule (this expedition)
At most one builder/committer in `.claude/worktrees/rlct` at a time (a second `lake build` corrupts `.lake`;
two `git commit`s race the index). Read-only auditors may run alongside one builder. Rungs on the same file
serialize. R1 (tooling/`scripts`), R0 (read-only recon), and G1 (geometry, disjoint files) can be dispatched
concurrently *only* if they touch disjoint paths + one builder rule holds — otherwise serialize.

_Updated each tick._
