# Statement card - A4 Case 2 residual-block entries

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `2586b46`.

Names:

- `DLNFibre.DLN.Aoyagi.case2ResidualBlockRows`
- `DLNFibre.DLN.Aoyagi.case2ResidualBlockCols`
- `DLNFibre.DLN.Aoyagi.case2ResidualBlockPivotEntries`
- `DLNFibre.DLN.Aoyagi.mem_case2ResidualBlockRows`
- `DLNFibre.DLN.Aoyagi.mem_case2ResidualBlockCols`
- `DLNFibre.DLN.Aoyagi.mem_case2ResidualBlockPivotEntries_iff`
- `DLNFibre.DLN.Aoyagi.case2_displayedPivot_mem_residualBlockPivotEntries_of_cont`

## Statement

For corrected Case 2, Lean records the finite candidate selected entries in
the residual-block center:

```text
rows:    J+1 <= i <= mu_S,
columns: J+1 <= j <= n_(S+1).
```

It proves the membership criterion for the product set and proves that the
displayed source pivot `(J+1,J+1)` is one candidate selected entry under the
continuation bound `J+1 <= mu_(S+1)`.

## Source role

Aoyagi displays the pivot chart at `d_(J+1,J+1)`, while the residual block
center contains every entry in the row range `J+1..M(S)` and column range
`J+1..M^(S+1)`. This artifact records that finite family without claiming chart
coverage.

## Proved

- Case 2 residual rows are indexed by prefix minimum `mu_S`.
- Case 2 residual columns are indexed by actual width `n_(S+1)`.
- The finite product set has the expected membership criterion.
- The displayed pivot entry belongs to this product set under continuation.

## Not proved

- No selected-entry chart construction.
- No proof that non-displayed selected entries satisfy the same transition.
- No chart cover theorem, permutation reduction, exponent update, regularity,
  normal-crossing certificate, or RLCT extraction.

## Status

- Sorry-free and xhigh source-scope reviewed at `2586b46`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
