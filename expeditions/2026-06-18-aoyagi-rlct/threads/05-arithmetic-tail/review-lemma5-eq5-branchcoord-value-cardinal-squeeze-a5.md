# Review - Lemma 5 Eq5 branch-coordinate/value cardinal squeeze

Date: 2026-06-22.

Reviewer: Godel, xhigh independent landed-slice review.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
- `reproduction-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md`
- `statement-card-a5-lemma5-eq5-branchcoord-value-cardinal-squeeze.md`

## Findings

No findings.

## Verdict

Pass.

The new Lean slice keeps the branch-coordinate map, coordinate correctness,
`branchS` left-endpoint formula, `branchK`/value relation, terminal Eq5
payloads, terminal `(p, alpha)` injectivity, terminal-label nonbase
inequality, and endpoint-base label explicit.  The wrappers only derive
selected-block membership and the Sigma-label value relation, then delegate to
the existing value-label and pAlpha cardinal-squeeze theorems.

## Nonclaims Checked

The artifacts do not claim Eq5 branch construction, source branch-coordinate
correctness, source branch-label formulas, direct counted-datum back-to-label
coverage, source-backed no-extra coverage, Lemma 5 order count, pole order,
normal crossings, or RLCT extraction.

## Verification Noted By Reviewer

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`
