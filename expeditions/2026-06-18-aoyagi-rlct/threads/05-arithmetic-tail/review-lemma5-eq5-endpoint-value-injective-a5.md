# Review - Lemma 5 Eq5 endpoint raw value injectivity

Date: 2026-06-22.

Reviewer: Dalton, xhigh independent landed-slice review.

Scope:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`
- `reproduction-lemma5-eq5-endpoint-value-injective-a5.md`
- `statement-card-a5-lemma5-eq5-endpoint-value-injective.md`

## Verdict

Pass after small statement-card metadata edits, now applied.

The Lean theorem shape and proof are correct.  The raw value-injectivity
theorem handles the endpoint collision cases:

- strict-strict collisions use supplied `alphaOf` injectivity;
- upper-strict collisions are excluded because alpha `0` is not in the strict
  Eq5 alpha domain;
- rising lower-strict collisions are excluded because alpha `j` is not in the
  strict domain;
- rising upper-lower collisions use the positive interior gap, so `j=1` is
  covered and `j=0` is correctly excluded by the interior-coordinate
  hypothesis.

The constructor wrapper removes only raw value injectivity and raw
disjointness.  It still requires base-value membership, alpha coverage,
strict/endpoint value formulas, strict alpha injectivity, and component
coordinate facts.

## Nonclaims checked

The documentation does not claim source branch construction, source-label
legality, endpoint-record distinctness as a source fact, base-filter survival,
classifier/order-count coverage, pole order, normal crossings, or RLCT.

## Verification noted by reviewer

The reviewer ran the focused Lean check and whitespace check.  Controller
landing verification is recorded in the statement card.
