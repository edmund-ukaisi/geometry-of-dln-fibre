# Review - A4 Case 1/Case 2 selected-entry finite coverage

Date: 2026-06-23.

Reviewer: xhigh read-only reviewer `Euler`.

Status: passed.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-case1-case2-selected-entry-finite-coverage-a4.md`;
- `statement-card-a4-case1-case2-selected-entry-finite-coverage.md`.

The review checked whether the new Case 1 and Case 2 wrappers are merely
definitional specializations of the generic selected-entry finite coverage
theorem, whether they use the correct nonempty finite centers, and whether
their statements/docstrings avoid analytic or source-production overclaims.

## Findings

No findings.

The private alias is a definitional restatement of the generic selected-entry
coverage theorem.  The generic certificate has `numCharts := center.card` and
delegates each chart map to the selected-entry chart at the pivot selected by
the finite chart equivalence.

The Case 2 wrapper specializes exactly to
`case2ResidualBlockPivotEntries n S J`, using the same `hS`, `hcont`, and
nonempty witness as the Case 2 all-pivot certificate definition.

The Case 1 wrapper specializes exactly to
`case1CenterGenerators n S J J1`, using the same unconditional nonempty
old-generator witness as the Case 1 all-pivot certificate definition.

The docstrings correctly limit the claim to finite chart-map coverage and
explicitly avoid source production, analytic atlas coverage, normal crossings,
pole order, and RLCT extraction.

## Verification

The reviewer ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

The focused build passed.

## Verdict

Acceptable to checkpoint.
