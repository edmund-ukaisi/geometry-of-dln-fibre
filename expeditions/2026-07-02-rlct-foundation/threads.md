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
| R2a | build (analysis) | r2a-threshold | ✅ LANDED `c06a6f54` (rlct-r2) — reviewing | cite-free `RLCT.integrabilityThreshold` + `|·|→1` witness + down-set + germ-mono; axiom-clean. Controller-verified (build 3854, sorries 0; RLCT-ns audit clean). `rev-r2a` auditing the ℝ-`IntegrableOn` fidelity. Under decision A: the cite-free **connecting interface** (threshold = pole λ via cited equivalence). Merge after review + gate-coverage fix. |
| R2b | build (analysis) | (formaliser next) | ⏳ **certificate DONE** — queued behind R2a merge + gate-coverage | **DECISION: A — zeta-pole `(λ,m)`.** `pp-zeta-cert` certificate LANDED (SOUND; decorrelated Codex gpt-5.4 exit 0; `threads/pp-zeta-cert/certificate.md`). The **bullet = ONE bundled continuation cite** (Atiyah 1970 + Saito/SLT: `∫|F|^s φ` continues meromorphically, poles ⊂ ℚ_{<0}, largest pole `s₀=−rlct_x` — *bundled* with the threshold identity, not bare). `λ/m` extraction + R2a threshold + Link 3 (real=complex codim, `codimRealFibre_eq_codimRepCanonical_baseChange`) all BUILT/PROVED. Net: opaque `rlctReal` axiom → constructed object on 1 cite. 7 formaliser warnings (sign `λ=−s₀`; smooth `φ` not `1_U`; no 2nd ½ on squared loss; Link1 bundled; local/global; `m≠θ`). Build `Core/Analysis/RLCT/{Zeta,Cited}` against the cert, hybrid-structured (payoff rides cite-free threshold; cont. cite buys `m`). |
| R3–R8 | — | — | ⛔ blocked on R2b | the RLCT foundation + payoff rewire. |

**Cordon coverage TODO (near-term):** the default gate `scripts/cited` scopes to `--ns DLNFibre`, so first-party **bare-namespace** modules (`RLCT`, and the L7 Mathlib-mirror namespaces) aren't audited by default (they audit clean under `--ns RLCT`). Extend the gate to cover first-party bare namespaces BEFORE the cited continuation axiom lands (it will live in a `RLCT` `Cited.lean`) — do it around the R2a merge.

## Concurrency rule (this expedition)
At most one builder/committer in `.claude/worktrees/rlct` at a time (a second `lake build` corrupts `.lake`;
two `git commit`s race the index). Read-only auditors may run alongside one builder. Rungs on the same file
serialize. R1 (tooling/`scripts`), R0 (read-only recon), and G1 (geometry, disjoint files) can be dispatched
concurrently *only* if they touch disjoint paths + one builder rule holds — otherwise serialize.

_Updated each tick._
