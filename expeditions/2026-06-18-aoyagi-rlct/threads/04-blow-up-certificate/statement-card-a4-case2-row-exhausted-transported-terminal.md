# Statement card - A4 Case 2 row-exhausted transported terminal

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2_not_next_cont_of_prefixMin_current_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalTransportedRows`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_eq_transportedRows`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SuppliedTerminalCprimeBridge.of_transportedRows`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSuffix_entryIdeal_eq_prefixProduct_of_rowExhausted`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`

## Statement

Lean now records the current-prefix row-exhausted stopped branch.  If
`prefixMinNat n S=J+1`, then the next displayed Case 2 continuation bound
fails.  The stopped terminal-prefix product can therefore be stated with the
terminal prefix candidate, and also with an explicit transported-row terminal
matrix whose last row is the top row of `Q^-1 C`.

## Proved

- Current-prefix row exhaustion forces `not (J+2 <= prefixMinNat n (S+1))`.
- The source-row terminal `C'` candidate equals the explicit transported-row
  matrix.
- The transported-row matrix supplies `SuppliedTerminalCprimeBridge`.
- The source old-top/source suffix theorem can be restated in the
  row-exhausted branch with the terminal-prefix product candidate.
- The same theorem can be rewritten through the explicit transported-row
  terminal matrix.

## Not Proved

- No actual next-width exhaustion.
- No original-row equality for row `J+1`.
- No recurrence/exponent relabel to `(S+1,0)`.
- No source-produced `C'^(S+1)`.
- No chart coverage, Jacobian arithmetic, normal crossings, RLCT extraction,
  termination, transition invariant, automatic Case 2 gap/tail transport, or
  printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-row-exhausted-transported-terminal-a4.md`.
- Review artifact:
  `review-case2-row-exhausted-transported-terminal-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
