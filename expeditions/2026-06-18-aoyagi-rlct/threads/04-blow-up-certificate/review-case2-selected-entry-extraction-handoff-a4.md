# Review - A4 Case 2 selected-entry extraction handoff

Date: 2026-06-24.

Reviewer: Goodall, xhigh read-only review.

Status: passed with no blocking findings.

## Scope

Reviewed the Lean theorem

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.lambda_and_poleOrder_eq_selectedCoordinateCount_div_two_and_one_of_extractionHypothesis
```

in `SelectedEntryNormalCrossing.lean`, the reproduction note, statement card,
and the expedition ledger updates for the Case 2 selected-entry extraction
handoff.

## Findings

No blocking findings.

The theorem stays inside the claimed dependency boundary.  The proof uses only
the chart-level extraction projections

```text
ExtractionHypothesis.lambda_eq_exponentMinimum
ExtractionHypothesis.theta_eq_exponentOrder
```

and then rewrites with the existing finite Case 2 selected-entry minimum and
order lemmas.  The finite lemmas themselves are the local selected-entry
certificate facts, not analytic chart-production claims.

Boundary fidelity is good.  The reproduction note, statement card, thread
entry, theorem ledger, synthesis, claims, and priorities notes all say that
the extraction hypothesis is consumed, not constructed.  They also disclaim
analytic coverage, transition regularity, arbitrary-pivot source production,
global A0 data, Aoyagi Theorem 2 order data, and RLCT extraction.

Source discipline is clean.  The reproduction anchors to Aoyagi PDF pp. 19-21
and pp. 5-6 plus the established A0 extraction interface, with no quiver-paper
dependency in the inspected handoff docs.

Lean hygiene is clean by source inspection.  The target file has no `sorry`,
`axiom`, `native_decide`, `#exit`, `unsafe`, or `admit`, and no broad new
imports.

## Residual Risk

The independent review was read-only and did not itself run Lean.  The
controller separately ran the focused module build, full `DLNFibre` build,
project sorry audit, and diff whitespace check.
