# Review - A4 selected-entry transition microcertificate evaluation

Reviewer: Confucius the 2nd (`xhigh`)
Date: 2026-06-24.

## Findings

No Lean/math findings after fixing the stale reproduction status line.

The reviewer confirmed:

- the denominator is consistently the normalized target coordinate, not
  `u * denom`;
- target unit and target formal determinant statements remain target-chart
  data;
- the Case 2 wrappers preserve source-selected normalization without asserting
  source-target unit equality;
- the documentation does not claim analytic transition regularity, chart
  coverage, source production, analytic Jacobian/volume control, global normal
  crossings, pole order, or RLCT extraction.

## Checks

The reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
./scripts/sorries
git diff --check
```

with the Lean file passing, the scanner reporting
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`, and whitespace checks passing
for reviewed files.

The controller separately ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/sorries
git diff --check
```

with the target build passing and the scanner/whitespace gates clean.

## Residual Boundary

Source fidelity was checked against the existing A4 reproduction/review notes
for Aoyagi PDF pp. 19-22 rather than direct PDF extraction in the reviewer
environment.  This slice remains finite selected-entry chart algebra only.
