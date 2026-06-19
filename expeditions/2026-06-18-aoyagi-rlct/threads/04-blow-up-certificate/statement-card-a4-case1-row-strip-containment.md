# Statement card - A4 Case 1 row-strip containment

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `1a1f801`.

Names:

- `DLNFibre.DLN.Aoyagi.case1StripRows_subset_case2ResidualBlockRows`
- `DLNFibre.DLN.Aoyagi.case1StripCols_eq_case2ResidualBlockCols`
- `DLNFibre.DLN.Aoyagi.case1StripEntries_subset_case2ResidualBlockPivotEntries`
- `DLNFibre.DLN.Aoyagi.case1_displayedPivot_mem_residualBlockPivotEntries_of_bounds`

## Statement

Lean proves that the Case 1 row strip lies in the active residual block when
the explicit row-validity bound is supplied:

```text
J + J1 <= mu_S.
```

The column range is definitionally the same actual-width range
`J+1..n_(S+1)`. Under the finite entry bounds `1 <= J1`,
`J+J1 <= mu_S`, and `J+1 <= n_(S+1)`, the displayed pivot
`(J+1,J+1)` lies in the residual-block entry set.

## Source role

This records the missing source-validity condition for the Case 1 row strip:
the row strip must fit inside the active residual rows. It keeps the actual
active column width separate from prefix minima.

## Proved

- Case 1 strip rows are contained in residual-block rows under
  `J+J1 <= mu_S`.
- Case 1 strip columns equal residual-block columns by definition.
- Case 1 strip entries are contained in residual-block entries under the same
  row bound.
- The displayed Case 1 pivot entry lies in the residual block under the finite
  row and column bounds.

## Not proved

- No Case 1 first-jump hypothesis.
- No old-label validity, level, minimality, or comparability.
- No selected-entry chart construction, chart coverage, `Q/P` transition,
  regularity/Jacobian fact, exponent update, transition invariant,
  termination proof, normal-crossing certificate, or RLCT extraction.

## Status

- Sorry-free and xhigh source-scope reviewed at `1a1f801`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
