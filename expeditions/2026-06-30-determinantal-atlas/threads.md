# Threads — `determinantal-atlas`

Per-rung formaliser/reviewer threads (the ladder is in [`priorities.md`](priorities.md)). One **builder/committer**
per shared worktree at a time; read-only auditors run concurrently. Controller integrates + re-gates per
[`loop-prompt.md`](loop-prompt.md).

## P0 — recon

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P0 | scout | dispatching | 🔄 | map current DLN rank-chart/bundle machinery + Mathlib coverage (determinantal ideals, `Matrix.rank`, iterated `Localization.Away`, `FiberBundle`); **the build-vs-cite verdict on the residue-field-rank bridge**; refine the P1/P2 ladder + de-DLN-ify target list |

## Phase 1 — foundation (`det-atlas-p1`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P1.a | — | — | ⏳ gated on P0 | localization-overlap API |
| P1.b–e | — | — | ⏳ gated on P0 | determinantal ideals · rank strata + cover · Schur coords · dimension |

## Phase 2 — constructive atlas + capstone (`det-atlas-p2`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P2.a–b | — | — | ⏳ | pivot-chart datum + fibre model · transitions |
| P2.c | — | — | ⏳ CRUX | cocycle compatibility — decorrelated review |
| P2.d | — | — | ⏳ CRUX (recon-gated) | bare `FiberBundle` capstone / residue-field-rank bridge — build iff detail-at-scale |

## Concurrency rule (this expedition)
At most **one builder/committer** in `.claude/worktrees/det-atlas` at a time (a second `lake build` corrupts
`.lake`; two `git commit`s race the index). Read-only auditors (no build, no commit) may run alongside one
builder. Rungs touching the same file are serialized.

_Updated each tick._
