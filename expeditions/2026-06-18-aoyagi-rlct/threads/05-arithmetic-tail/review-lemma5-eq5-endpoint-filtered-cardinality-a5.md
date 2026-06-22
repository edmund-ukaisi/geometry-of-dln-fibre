# Review - Lemma 5 Eq5 endpoint filtered cardinality

Date: 2026-06-22.

Reviewer: Harvey, xhigh independent landed-slice review.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `reproduction-lemma5-eq5-endpoint-filtered-cardinality-a5.md`
- `statement-card-a5-lemma5-eq5-endpoint-filtered-cardinality.md`

## Findings

No findings.

## Verdict

Pass.

The three Lean declarations stay within supplied-family cardinality
specialization.  The general endpoint theorems keep raw value injectivity and
raw cross-coordinate disjointness explicit.  The strictest endpoint theorem
exposes supplied strict alpha injectivity plus branch-coordinate/component
coordinate facts and derives only those two raw hypotheses.

## Nonclaims Checked

The artifacts frame the result as finite supplied bookkeeping and explicitly
defer source branch construction, source-label legality, base-filter survival
for source records, terminal-minimum/source-backed coverage, pole order,
normal crossings, and RLCT extraction.

## Verification Noted By Reviewer

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
