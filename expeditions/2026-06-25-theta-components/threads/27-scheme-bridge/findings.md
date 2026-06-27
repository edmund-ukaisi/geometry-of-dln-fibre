# Thread 27 — scheme-level cover→PivotDatum bridge (PR #11 review round 2) — certificate

**Formaliser tide (fix-bridge2), CLOSED.** Edited `Core/FibreBundleLocallyTrivialFull.lean` (already
wired). Whole library green (3806 jobs), sorries 0, all headlines axiom-clean `[propext,
Classical.choice, Quot.sound]` (controller-gated). Reviewer + Codex PASS, no overclaim. Commit
`62ce5993`.

## What it closes (owner round-2 r3484321684/r3484594963 follow-up)
The round-1 `pivotOfCover` took `Function.Injective s/t` as hypotheses, so a *scheme-level* consumer at
`p ∈ basicOpen (chartDsigAt d r s t)` still couldn't obtain a `PivotDatum`. Now closed with **no
external injectivity hypothesis**.

## Landed (axiom-clean)
- `ΔPdeepAt_eq_zero_of_not_injective_left` / `_right` — a repeated row/col ⟹ `ΔPdeepAt = 0`
  (`Matrix.det_zero_of_row_eq` / `_column_eq`; the det-zero step is *literally* a `submatrix` det —
  `ΔPdeepAt = ((Matrix.of (multPoly d)).submatrix s t).det` — so the row/col-repeat reduction was clean,
  NO deep-minor obstruction).
- `chartDsigAt_eq_zero_of_not_injective` — `chartDsigAt = 0` (quotient class of the vanishing minor).
- `injective_of_mem_basicOpen_chartDsigAt {p} (hp : p ∈ basicOpen (chartDsigAt d r s t)) :
  Injective s ∧ Injective t` — contrapositive (`mem_basicOpen` + `0 ∈ p.asIdeal`).
- `pivotDatumOfMemBasicOpen … (hmem : p ∈ basicOpen (chartDsigAt d r s t)) :
  {I : PivotDatum d r hp hq // pivotElt … I = chartDsigAt d r s t}` — the standalone scheme-level bridge.
- atlas FIELD `pivotOfBasicOpen` on `PivotLocalProductAtlas` (wired in `pivotLocalProductAtlas`): a
  scheme-cover consumer gets `triv (pivotOfBasicOpen …)` with nothing to discharge.
- A new witness `example` exercises `pivotOfBasicOpen` with no injectivity hyp. `pivotOfCover` (taking
  injectivity) kept for the point-set `cover` field.

## Scope note (reviewer, not a defect)
The lemmas do not assert unconditional chart non-emptiness for all `(d,r)` (degenerate `r=0` / empty
`Σ^r` ⟹ zero ring); the prose claims only mechanism-genuineness + API-usability, correctly scoped.

## Net (PR #11 review)
Round 1: C1 closed (`pivotOfCover`), C2 base-side restriction, C3 arbitrary-B, C4 non-vacuity, C5
deprecate. Round 2: 5 doc/precision fixes + **this scheme-level bridge closes the consumability gap the
round-1 `pivotOfCover` left** (the C1 follow-up). The atlas is now genuinely consumable scheme-side.
Artifacts: `threads/27-scheme-bridge/statement-card.md` (reviewed). Lean: `Core/FibreBundleLocallyTrivialFull.lean`.
