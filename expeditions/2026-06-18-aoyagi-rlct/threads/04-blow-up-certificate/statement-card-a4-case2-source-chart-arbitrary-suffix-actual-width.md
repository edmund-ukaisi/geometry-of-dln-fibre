# Statement card - A4 Case 2 source-chart arbitrary-suffix actual-width boundary

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopSuppliedSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary`

## Statement

Lean should expose the concrete displayed source-chart actual-width terminal
boundary with the remaining following product kept as an arbitrary supplied
matrix `F : Matrix τ υ R`.

The theorem still assumes the displayed Case 2 stage and continuation
hypotheses (`hS`, `hSL`, `hcont`), actual-width exhaustion `n(S+1)=J+1`,
pre-state exponent certificates, level invariants, the least-value gap, and a
supplied residual-block `chartFamily`.

## Proved

- The displayed source chart fixes the successor recurrence state to
  `pre.case2Succ(chartMap(J+1,J+1))`.
- Under `n(S+1)=J+1`, the stopped terminal product uses original source rows
  `1..J+1`.
- The surviving terminal weight is read from the relabelled `(S+1,0)` state.
- The actual-width relabelled level invariant and exponent-domain certificate
  are packaged with the arbitrary-`F` entry-ideal equality.

## Not Proved

- `F` remains supplied.
- No chart coverage or atlas construction.
- No global source-produced `C'^(S+1)`.
- No proof that the following product is chart-produced.
- No row-exhausted wide-next original-row theorem.
- No Jacobian, normal-crossing/RLCT, termination, transition-invariance, or
  printed-vector repair theorem.

## Review

- Review artifact:
  `review-case2-source-chart-arbitrary-suffix-actual-width-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
