# Review - Lemma 5 Eq5 endpoint branch-coordinate disjointness

Date: 2026-06-22.

Reviewer: Noether, xhigh independent review.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `reproduction-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md`
- `statement-card-a5-lemma5-eq5-endpoint-branchcoord-disjoint.md`

## Verdict

Pass after small documentation edits, now applied.

The Lean statement shapes and proof idea are sound.  The disjointness theorem
proves exactly finite raw-set disjointness from supplied coordinate facts, and
the wrapper only removes the separate `branches_pairwiseDisjoint` hypothesis.
Raw value injectivity, base-value membership, alpha coverage, and endpoint
value assumptions remain supplied.

## Requested fixes

- Say "distinct interior coordinates" to match the Lean hypotheses
  `i,j in Finset.Icc 1 (ell - 1)`.
- Mark review and verification as complete in the statement card.
- Update the module comment so it no longer says this file proves no
  cross-coordinate disjointness at all; the new theorem derives only the
  supplied-coordinate version.

## Nonclaims checked

The slice does not construct Eq5 branches or endpoint records, prove
source-label legality, prove endpoint distinctness, prove base-filter
survival, prove value injectivity, construct a no-extra classifier, prove
normal crossings, prove pole order, or extract RLCT.

## Verification noted by reviewer

Reviewer ran focused Lean checks and found no `sorry`, `axiom`,
`native_decide`, or `#exit` in the reviewed Lean scope.  Controller verification
for landing is recorded in the statement card.
