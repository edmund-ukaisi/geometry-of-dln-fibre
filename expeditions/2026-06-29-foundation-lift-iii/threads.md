# Threads — `foundation-lift-iii`

Per-rung formaliser/reviewer threads (the ladder is in [`priorities.md`](priorities.md)). One **builder/committer**
per shared worktree at a time; read-only auditors run concurrently. Controller integrates + re-gates per
[`loop-prompt.md`](loop-prompt.md).

## Phase 1 — differential-algebra interface (`fl3-p1`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P1.1 | formaliser | aa0363b6 | ✅ DONE `333a038b` | two-file split → `Core/RingTheory/Kaehler/GenericRank.lean` + `Core/Dimension/Trdeg.lean`; green 3822, axiom-clean. Wrapper char-FREE; `[CharZero]` quarantined to `diffIndepCriterion_proof` |
| P1.2 | reviewer | a445e1fc | ✅ REVIEWED | crux verdict: **leave `[CharZero]`** — `[PerfectField]` swap is FALSE (`𝔽_p[T]`, `x=T^p`: `D(T^p)=0`; perfect-field falls on `Pf=k(X)`, perfect iff char 0). Codex-concurred. Fidelity PASS (145 lines byte-identical). Action: drop unused `[Fintype ι]` in `D_adjoin_mem_span`. Char-`p` criterion → roadmap |
| P1.3 | controller | — | ✅ VERIFIED (no edit) | `CotangentJacobian.lean` — orientation discipline exemplary; namespace+path mirror Mathlib |
| P1.4 | controller | — | ✅ VERIFIED (no edit) | `CotangentLocalization.lean` — name=content, minimal hyps (`[Field k]` not needed) |
| P1.5 + P1.6-V2 | formaliser | a41d8e0e | ✅ DONE `1dc6c698` | `MatrixKaehler.lean` split → `Core/RingTheory/Derivation/Matrix.lean` + `Core/LinearAlgebra/BaseChange.lean` (V2 + 3-way distinctness docstring); green 3823, axiom-clean. Caught + honestly fixed a severed transitive instance import (→ L6) |
| **P1-final** (P1.7 + P1.2-finish + P1.6-V1) | formaliser | dispatching | 🔄 | **P1.7 layering fix**: push `trdeg_eq_of_integral_injective` down off orbit-flavored `AffineNoetherRank`, break `Dimension/Localization→AffineNoetherRank` inversion, re-derive quotient lemma from `ringKrullDim_eq_trdeg_of_fg_domain`; **P1.2-finish** drop `[Fintype ι]`; **P1.6-V1** distinctness docstring |
| P1.6-V3 | controller | — | ✅ RESOLVED (no extraction) | V3 = Mathlib's `Module.Flat.linearIndependent_one_tmul`, already named+documented in `GenericRank`. Wrapping it would be an anti-Mathlib re-export |

## Phase 2 — orbit-dimension squeeze (`fl3-p2`, probe-gated)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P2.0 | formaliser | — | gated on Phase 1 | de-`Tuple` probe |

## Concurrency rule (this expedition)
At most **one builder/committer** in `.claude/worktrees/fl3` at a time (a second `lake build` corrupts `.lake`;
two `git commit`s race the index). Read-only auditors (no build, no commit) may run alongside one builder.
Rungs touching the same file are serialized.

_Updated each tick._
