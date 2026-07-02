# Threads — `rlct-foundation`

Per-rung formaliser/reviewer/scout threads (ladder in [`priorities.md`](priorities.md)). One
**builder/committer** per shared worktree at a time; read-only auditors alongside. Controller integrates +
re-gates per [`loop-prompt.md`](loop-prompt.md). Branch `expedition/rlct-foundation` (off `dev` `10edbdc3`).

## Status

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| R1 | build (SWE/infra) | (dispatched) | 🔄 CRUX | citation cordon: `@[cited]` attr + `collectAxioms` accounting core + `#audit_cited` + `scripts/cited` gate + adversarial tests + `docs/policies/citation-cordon.md`; retrofit `RlctRealInterface`. **Battle-test (fixtures = spec, guard-first).** Sole builder in `rlct` worktree. Decorrelated review (controller-spawned). |
| R0 | scout | (dispatched) | 🔄 read-only | Mathlib analytic-coverage recon + build-vs-cite reach (kill-questions in brief). Reports to controller; no edits. |
| G1 | formaliser | g1-fibre-theta | ✅ DONE (awaiting reviewer) | non-monotone fibre `θ` — DROPPED `Monotone d`. FLOOR: headline ends at `numTop d r` (`Monotone` was a thin E0-`cTheta` layer, not a fibration problem): `ncard_topDimMinPrimes_fibre_eq_numTop` (+`_of_rank`) + E0-geometric rung `ncard_topDimMinPrimes_sigma_eq_numTop`. CLOSED FORM (perm-invariance was LANDED, no new cite): `numTop_eq_cTheta_dminus_sort` → `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_sort` (+`_of_rank`) = `cTheta((d∘sort d)−r)` for arbitrary `d`. Two non-monotone witnesses `d=[1,2,1]`. Green (3836), sorry-free, axiom-clean. `origin expedition/rlct-g1` @ `a9bbb786`. Card: [`threads/g1-fibre-theta-nonmonotone.md`](threads/g1-fibre-theta-nonmonotone.md). |
| R2–R8 | — | — | ⛔ blocked on R1+R0 | the RLCT foundation + payoff rewire. |

## Concurrency rule (this expedition)
At most one builder/committer in `.claude/worktrees/rlct` at a time (a second `lake build` corrupts `.lake`;
two `git commit`s race the index). Read-only auditors may run alongside one builder. Rungs on the same file
serialize. R1 (tooling/`scripts`), R0 (read-only recon), and G1 (geometry, disjoint files) can be dispatched
concurrently *only* if they touch disjoint paths + one builder rule holds — otherwise serialize.

_Updated each tick._
