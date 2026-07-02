# Threads — `rlct-foundation`

Per-rung formaliser/reviewer/scout threads (ladder in [`priorities.md`](priorities.md)). One
**builder/committer** per shared worktree at a time; read-only auditors alongside. Controller integrates +
re-gates per [`loop-prompt.md`](loop-prompt.md). Branch `expedition/rlct-foundation` (off `dev` `10edbdc3`).

## Status

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| R1 | build (SWE/infra) | r1-cordon | ✅ **LANDED** `82c3b006` | citation cordon shipped + **controller-verified** (build 3836 green · gate `UNACCOUNTED=0 CITED=3 LOCATION=0` · sorries `0/3-axiom` · fixtures **13/13**). Parametric `@[cited]` + `collectAxioms` accounting (forget-proof) + `#audit_cited` + enforcing `scripts/cited` + 13 adversarial fixtures; retrofit `AoyagiCited.lean` (3 cites + proved interface + corner-0 payoff); `docs/policies/citation-cordon.md` graduated. Perf: `collectAxiomsBatch` (per-decl timed out >590 s → ~20 s). Aggregator-wired (controller). Codex-xhigh on design; **`rev-cordon` audit: SOUND** (batch = stdlib `collectAxioms`; fidelity OK; doc accurate) → hardened: fixture (f) opaque-hidden axiom + empty-source rejection + doc fix, **battle-test 17/17** (`f8b83751`). |
| R0 | scout | r0-recon | ✅ **DONE** (recon delivered) | **GREENFIELD**: `rlctAt`/`rlctAtOn`/`weightedThreshold` are NOT on `dev` (cross-worktree only; ROADMAP §4b claim stale). Strong BUILD base (Mellin+`cpow` pole, `meromorphicOrderAt` arith, multidim CoV + integrability transport, rpow dichotomy, JapaneseBracket, parametric holomorphy); monuments confirmed absent (cite); coord-change invariance BUILDABLE. Value-vs-pole first-slice flag → operator. Codex CLI down (env). |
| G1 | formaliser | g1-fibre-theta | ✅ **MERGED** (controller-reviewed) | non-monotone fibre `θ` — DROPPED `Monotone d`. Recon calibrated it: `Monotone` was a thin E0-`cTheta` layer, not a fibration problem. FLOOR: `ncard_topDimMinPrimes_fibre_eq_numTop` (+`_of_rank`) + E0-geometric rung `ncard_topDimMinPrimes_sigma_eq_numTop`. CLOSED FORM (perm-invariance was LANDED, no new cite): `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_sort` (+`_of_rank`) = `cTheta((d∘sort d)−r)` for arbitrary `d`. Two non-monotone witnesses `d=![1,2,1]` (shown in-file). Axiom-clean `[propext,Classical.choice,Quot.sound]`; Codex-reviewed (exit 0). Merged into `rlct-foundation`. |
| R2a | build (analysis) | r2a-threshold | 🔄 building | **definition-agnostic cite-free substrate** (safe under A/B/C): `Core/Analysis/RLCT/{Basic,Integrability}` — the integrability-**threshold** value (named `rlctThreshold`, NOT `rlct`) + 1-D `|t|→1` witness + (stretch) coord-change invariance. R0's recommended first slice; reused under every definition choice. Controller proceeded here (safe substrate) rather than idle; the definition headline (R2b) still awaits the operator. |
| R2b | build | — | ⏳ gated on **DEFINITION DECISION** (operator) | the RLCT **definition headline**: zeta-pole `(λ,m)` (operator's choice; needs cited continuation) vs value-as-def vs hybrid (controller rec). Declares "the RLCT" + connects it to the R2a threshold. Awaiting A/B/C. |
| R3–R8 | — | — | ⛔ blocked on R2b | the RLCT foundation + payoff rewire. |

## Concurrency rule (this expedition)
At most one builder/committer in `.claude/worktrees/rlct` at a time (a second `lake build` corrupts `.lake`;
two `git commit`s race the index). Read-only auditors may run alongside one builder. Rungs on the same file
serialize. R1 (tooling/`scripts`), R0 (read-only recon), and G1 (geometry, disjoint files) can be dispatched
concurrently *only* if they touch disjoint paths + one builder rule holds — otherwise serialize.

_Updated each tick._
