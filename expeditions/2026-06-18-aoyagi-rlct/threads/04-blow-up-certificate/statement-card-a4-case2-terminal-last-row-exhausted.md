# Statement card - A4 Case 2 terminal-last row-exhausted boundary

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`

## Statement

Lean exposes the row-exhausted transported-prefix terminal boundary in the
terminal-last case `S+1=L`, consuming Aoyagi's raw source suffix and removing
it as an empty product at the matrix-entry-ideal level.

## Proved

- Multiplication by the terminal-last source suffix does not change the
  matrix-entry ideal, after endpoint transport.
- Under current-prefix row exhaustion `prefixMinNat n S=J+1`, the stopped
  terminal side uses the transported terminal prefix rows.
- The displayed source-chart wrapper fixes the post state to the source chart
  map and corrected selected-label data, but does not relabel to `(S+1,0)`.

## Assumed

- The displayed Case 2 stage and continuation hypotheses.
- Current-prefix row exhaustion `prefixMinNat n S=J+1`.
- Terminal-last condition `S+1=L`.
- The pre-state exponent certificate, level invariant, and least-value gap.
- The residual-block chart-family regularity and transition interface.
- Finite source-layer types for the suffix endpoints.
- Supplied source following matrix data `C` and edge matrices `Ctail`.

## Cited

- None in Lean.  This is finite algebra and bookkeeping.

## Deferred

- Original-row equality for the row-exhausted wide-next branch.
- Relabelled `(S+1,0)` recurrence/exponent certificates for this branch.
- Chart coverage, source production of `C'^(S+1)`, chart-produced following
  products, Jacobian arithmetic, normal crossings/RLCT extraction,
  termination, transition invariance, and repair of the printed Case 2 vector
  mismatch.

## Review

- Review artifact:
  `review-case2-terminal-last-row-exhausted-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
