# Statement card - A4 Case 2 actual-width source-chart terminal boundary

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalOriginalRowsBoundary`

## Statement

Lean now packages the actual-width displayed source-chart terminal branch as a
boundary theorem.  It combines the original-row terminal source-suffix
entry-ideal equality with the actual-width relabelled level and exponent-domain
certificates for `(S+1,0)`.

## Proved

- Under `n(S+1)=J+1`, the source-chart terminal product uses original source
  rows `1..J+1`.
- The surviving terminal weight is read from the relabelled successor state
  `(pre.case2Succ chartValue).stageRelabelSuccZero`.
- The corrected selected-label exponent overrides and level invariants
  transport to state `(S+1,0)`.

## Not Proved

- No source-produced `C'^(S+1)`.
- No row-exhausted wide-next original-row theorem.
- No chart coverage or atlas construction.
- No chart-produced post-data, Jacobian, normal-crossing/RLCT, termination, or
  transition-invariance theorem.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
