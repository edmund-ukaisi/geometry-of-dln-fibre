# Statement card - A4 Case 2 source-chart terminal source-suffix

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`

## Statement

Lean now composes the concrete displayed source-chart boundary constructor
with the terminal source-suffix wrappers.  The post recurrence state is
`pre.case2Succ(case2DisplayedSourceChartMap(...)(J+1,J+1))`, and the exponent
post-data are the corrected selected-label overrides.

## Proved

- In the actual-width branch `n(S+1)=J+1`, the source-chart terminal
  source-suffix product can be rewritten with original terminal rows
  `1..J+1` and relabelled successor weight.
- In the row-exhausted branch `prefixMinNat n S=J+1`, the same source-chart
  product can be rewritten with terminal-prefix transported rows.
- The row-exhausted pivot row remains the top row of `Q^-1 C`.

## Not Proved

- No chart coverage or atlas construction.
- No global source-produced `C'^(S+1)`.
- No proof that `C` or `Ctail` are chart-produced.
- No Jacobian, normal-crossing, RLCT, termination, or transition-invariance
  theorem.
- No `(S+1,0)` recurrence relabel in the row-exhausted branch.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-source-chart-terminal-source-suffix-a4.md`.
- Review artifact:
  `review-case2-source-chart-terminal-source-suffix-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
