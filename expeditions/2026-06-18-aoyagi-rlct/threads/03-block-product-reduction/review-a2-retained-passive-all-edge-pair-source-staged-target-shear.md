# Review - A2 retained-passive all-edge pair source-staged target shear

Date: 2026-06-27.

Status: PASS.

## Scope

This review covers the all-edge retained-passive source-staged `(F2,C)`
target package in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`, with the
matching reproduction and statement card:

- `reproduction-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`;
- `statement-card-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`.

## Checks

Xhigh read-only reviewer `Dewey` checked that
`retainedPassiveSourceStagedSuccessorF2` is typed over `q.succ`, not
`q.castSucc`.  Its `castSucc` branch uses the source tangent
`v.F2_(p.succ)` transported by `(Fin.succ_castSucc p).symm`, and its terminal
branch is the appended zero.

The all-edge equality theorem splits the retained edge by `Fin.lastCases`.
The terminal branch uses the landed terminal edge-pair package and cancels
only the staged terminal zero term.  The nonterminal branch uses the landed
source-staged one-step theorem.

The source-pair recovery theorem rewrites the staged family to the formal
edge-pair family and then applies
`retainedPassiveFormalRawF2CLinearEquivAt_symm_recovers_sourcePair`.

## Verdict

PASS.  No mathematical or Lean fixes required.  The only review nit was stale
statement-card status text, updated after the review.

## Nonclaims Preserved

This package is not a determinant-one target-side shear, not a target-side
`LinearEquiv`, not an actual derivative determinant comparison, not a
descending induction over the whole target-side construction, not a measure
transport theorem, not normal crossings, not pole order, and not RLCT.
