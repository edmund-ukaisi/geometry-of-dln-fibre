# Threads — `determinantal-atlas`

Per-rung formaliser/reviewer threads (the ladder is in [`priorities.md`](priorities.md)). One **builder/committer**
per shared worktree at a time; read-only auditors run concurrently. Controller integrates + re-gates per
[`loop-prompt.md`](loop-prompt.md).

## P0 — recon

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P0 | scout | a687ac4d | ✅ DONE `787e688f` | verdict: mostly re-home/de-DLN-ify (overlap API + cover already built; residue bridge already proved); **capstone = BUILD** as a bespoke Zariski predicate over the rank-`r` open (NOT Mathlib `FiberBundle`, NOT over the closure). Refined ladder in `priorities.md`; report `threads/p0-recon/report.md` |

## Phase 1 — foundation (`det-atlas-p1`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| **P1.a** | formaliser | dispatching | 🔄 | overlap API **re-home** (`FibreBundleTransition` §Abstract+§Triple, triple cocycle proved) → `Core/RingTheory/Localization/Overlap.lean`; retarget 2 consumers (L6). Lowest-risk |
| P1.b–e | — | — | ⏳ | determinantal `(r+1)`-minor ideal (new) · rank strata + cover (re-home) · Schur coords (re-home) · dimension (Brick A cited) |

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
