# Statement card - A4 Case 2 terminal-last actual-width boundary

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.matrixEntryIdeal_mul_ndrec_one`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_originalRowsProduct_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalLastOriginalRowsBoundary`

## Statement

Lean exposes the displayed source-chart actual-width terminal boundary in the
terminal-last case `S+1=L`, consuming Aoyagi's raw source suffix and removing
it as an empty product.

## Proved

- Multiplication by the terminal-last source suffix does not change the
  matrix-entry ideal, after endpoint transport.
- Under actual-width exhaustion `n(S+1)=J+1`, the stopped terminal product uses
  original source rows `1..J+1`.
- The source-suffix terminal-last entry-ideal equality is packaged with the
  actual-width relabelled level invariant and exponent-domain certificate.

## Assumed

- The displayed Case 2 stage and continuation hypotheses.
- Terminal-last condition `S+1=L`.
- Actual-width exhaustion `n(S+1)=J+1`.
- The pre-state exponent certificate, level invariant, and least-value gap.
- The residual-block chart-family regularity and transition interface.
- Finite source-layer types for the suffix endpoints.
- Supplied source following matrix data `C` and edge matrices `Ctail`.

## Cited

- None in Lean.  This is finite algebra and bookkeeping.

## Deferred

- Row-exhausted wide-next terminal-last wrapper.
- Chart coverage, source production of `C'^(S+1)`, chart-produced following
  products, Jacobian arithmetic, normal crossings/RLCT extraction,
  termination, transition invariance, and repair of the printed Case 2 vector
  mismatch.

## Review

- Review artifact:
  `review-case2-terminal-last-actual-width-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
