# Review - Lemma 5 Eq5 endpoint counted-datum classifier

Date: 2026-06-22.

Reviewer: Hypatia, xhigh independent landed-slice review.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `reproduction-lemma5-eq5-endpoint-countdatum-classifier-a5.md`
- `statement-card-a5-lemma5-eq5-endpoint-countdatum-classifier.md`

## Verdict

Initial verdict: fail for documentation/API-surface issues.  Lean itself
passed.

The issues were:

- the classifier Lean name in the notes omitted the
  `AoyagiLemma5SuppliedNonbaseFamily` namespace;
- the documentation omitted the Lean hypothesis `a <= ell`;
- the statement card verification field was stale.

These issues were repaired before landing.

Follow-up independent re-review by Dirac found one remaining module-comment
issue: the file-level docstring still said the file constructs no classifiers,
while this slice adds a supplied-full-branches classifier wrapper.  The
docstring now states the narrower truth: the classifier wrapper is only for
supplied full branches from the strictest endpoint constructor and does not
classify source terminal-minimum labels or prove no-extra coverage.

## Lean Review

The proof shape is correct.  The branch-coordinate theorem only unfolds the
strictest endpoint constructor, strips the base-value filter to raw membership,
and applies the supplied component-coordinate adapter.  The classifier is
exactly for that constructor's supplied `fullBranches`; it does not claim
terminal-minimum/source-label/no-extra coverage.

## Nonclaims checked

The slice does not construct Eq5 strict branches or endpoint records, prove
source-label legality, prove the coordinate map is source-produced, prove
base-filter survival, prove endpoint distinctness, classify source
terminal-minimum labels, prove no-extra coverage, prove pole order, prove
normal crossings, or extract RLCT.

## Verification noted by reviewer

The reviewer ran the focused Lean check and whitespace check and found no
focused `sorry`/`admit`/`axiom`/`unsafe` hits.  Controller landing verification
is recorded in the statement card.
