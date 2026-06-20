# Statement card - A4 Case 2 terminal frontier bridges

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.pivotQinv_mul_top_apply`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperCprimeTop_apply`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperCprimeTop_apply_of_width_next_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperCprimeTop_eq_sourceRow_of_width_next_eq`
- `DLNFibre.DLN.Aoyagi.case2SourceTerminalPrefixRowIndex`
- `DLNFibre.DLN.Aoyagi.case2SourceTerminalRowEquivPrefix`
- `DLNFibre.DLN.Aoyagi.case2SourceTerminalRowEquivPrefixOfNotNext`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalOriginalRows`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_eq_originalRows_of_width_next_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_oldRow`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_pivotRow`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SuppliedTerminalCprimeBridge`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_eq_of_oldRows_pivotRow`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_suppliedCterm_mul`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SuppliedTerminalCprimeBridge.cprimeCandidate_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SuppliedTerminalCprimeBridge.of_originalRows_width_next_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SuppliedTerminalCprimeBridge.terminalProduct_eq_weight_mul_Cterm_mul`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SuppliedTerminalCprimeBridge.cprimePrefixCandidate_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.SuppliedTerminalCprimeBridge.terminalPrefixProduct_eq_weight_mul_CtermPrefix_mul`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalWeightPrefixCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimePrefixCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalProductPrefixCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_cprimePrefixCandidate_mul`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.matrixEntryIdeal_sourceTerminalProductPrefixCandidate_eq_sourceTerminalProduct`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalPrefixProduct_of_not_next_cont`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalPrefixProduct_of_not_next_cont`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_oldTopSourceSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth`

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
- The top row of `Q^-1 C` expands as the old pivot-column row plus the
  displayed pivot-row weighted post-pivot column sum.
- Under actual next-width exhaustion `n(S+1)=J+1`, the post-pivot column
  complement is empty and the top row of `Q^-1 C` is the original source row
  `C(J+1,-)`.
- In that actual-width subcase, the source-row terminal `C'` candidate equals
  the original source rows `1..J+1`, and the supplied terminal bridge can be
  instantiated with those rows.
- The prefix-row product candidate has the expected product form.
- The stopped source old-top/source suffix theorem can be restated with the
  prefix-row product candidate on the right.
- A supplied terminal matrix satisfying explicit old-row and pivot-row
  equations can replace the candidate in the terminal product.
- The same row equations are packaged as a named supplied bridge for later
  chart-production work.
- The supplied bridge rewrites the terminal-prefix product and the stopped
  source old-top/source suffix theorem through the supplied terminal `Cterm`,
  including the prefix-row source-suffix theorem.
- The actual-width old-top/source-suffix terminal theorem can be specialized
  to the original source rows `1..J+1`.

## Not Proved

- No chart production of the supplied terminal matrix.
- No construction of actual rows beyond the terminal prefix object.
- No recurrence/exponent relabel beyond the already separate actual-width
  theorem.
- No weakening of the original-row bridge to failed next-continuation,
  prefix exhaustion, or row-exhaustion cases.
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
