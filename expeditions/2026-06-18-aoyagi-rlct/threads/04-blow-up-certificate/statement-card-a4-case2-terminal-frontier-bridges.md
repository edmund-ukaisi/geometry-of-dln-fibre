# Statement card - A4 Case 2 terminal frontier bridges

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2SourceTerminalPrefixRowIndex`
- `DLNFibre.DLN.Aoyagi.case2SourceTerminalRowEquivPrefix`
- `DLNFibre.DLN.Aoyagi.case2SourceTerminalRowEquivPrefixOfNotNext`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_oldRow`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_pivotRow`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_eq_of_oldRows_pivotRow`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_suppliedCterm_mul`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalWeightPrefixCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimePrefixCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalProductPrefixCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_cprimePrefixCandidate_mul`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.matrixEntryIdeal_sourceTerminalProductPrefixCandidate_eq_sourceTerminalProduct`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalPrefixProduct_of_not_next_cont`

## Statement

Lean now records two bridges for the stopped displayed Case 2 terminal
frontier:

- Under continuation plus failed next continuation, the source terminal row
  type `1..J+1` is equivalent to the terminal prefix row type `1..M(S+1)`.
- Any supplied terminal matrix whose old rows are unchanged and whose pivot
  row is the top row of `Q^-1 C` rewrites the existing source-row terminal
  product candidate.

## Proved

- `M(S+1)=J+1` under `J+1<=M(S+1)` and not `J+2<=M(S+1)` is used to build a
  row equivalence.
- The source terminal weight, `C'` candidate, and product candidate can be
  reindexed onto terminal prefix rows `1..M(S+1)`.
- The prefix-row product candidate has the expected product form.
- The stopped source old-top/source suffix theorem can be restated with the
  prefix-row product candidate on the right.
- A supplied terminal matrix satisfying explicit old-row and pivot-row
  equations can replace the candidate in the terminal product.

## Not Proved

- No chart production of the supplied terminal matrix.
- No construction of actual rows beyond the terminal prefix object.
- No recurrence/exponent relabel beyond the already separate actual-width
  theorem.
- No chart coverage, coordinate regularity, Jacobian arithmetic, normal
  crossings, RLCT extraction, termination, transition invariant, automatic
  Case 2 gap/tail transport, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-terminal-frontier-bridges-a4.md`.
- Review artifact:
  `review-case2-terminal-frontier-bridges-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
