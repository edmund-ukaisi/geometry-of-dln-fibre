# Statement card - A4 Case 2 source terminal product candidate

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`
- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.matrixEntryIdeal_submatrix_equiv`
- `DLNFibre.DLN.Aoyagi.case2SourceTerminalRowIndex`
- `DLNFibre.DLN.Aoyagi.case2SourceTerminalRowEquiv`
- `DLNFibre.DLN.Aoyagi.case2SourceTerminalRowEquiv_inl`
- `DLNFibre.DLN.Aoyagi.case2SourceTerminalRowEquiv_inr`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceTerminalCprimeCandidate`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceTerminalCprimeCandidate_submatrix_terminalRowEquiv`
- `DLNFibre.DLN.Aoyagi.matrixEntryIdeal_case2DisplayedSourceTerminalCprimeCandidate_eq_terminalCnext`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceTerminalWeight`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceTerminalProductReindexedCandidate`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceTerminalProductReindexedCandidate_eq_terminalCprimeCandidate_submatrix`
- `DLNFibre.DLN.Aoyagi.matrixEntryIdeal_sourceTerminalProductReindexedCandidate_eq_terminalCprimeCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont`

## Statement

Lean now packages the stopped displayed Case 2 terminal candidate in one-based
source-row order.  The stacked row type

```text
case2SourceOldTopRowIndex J ⊕ Unit
```

is reindexed to

```text
case2SourceTerminalRowIndex J = {1,...,J+1}.
```

The stopped source old-top theorem with the named suffix product is restated
with this one-based source-row terminal product candidate on the right hand
side.

## Proved

- Entry ideals are invariant under row/column reindexing by equivalences.
- Old source rows plus the surviving pivot row are equivalent to source rows
  `1,...,J+1`.
- The source-row terminal next matrix reindexes back to the existing stacked
  terminal next matrix.
- The source-row terminal product candidate has the same matrix-entry ideal as
  the existing stacked stopped terminal candidate.
- The stopped displayed Case 2 source old-top/source suffix theorem can be
  restated with the source-row reindexed terminal product candidate.

## Assumed

- The stopped displayed Case 2 supplied chart-family boundary.
- Failed next continuation.
- The raw suffix product from `sourceSuffixProduct`.

## Not Proved

- No chart-produced `C'^(S+1)`.
- No proof that the source-row terminal candidate is Aoyagi's full transformed
  source matrix rather than a row presentation of supplied terminal data.
- No chart coverage, coordinate regularity, Jacobian arithmetic, normal
  crossings, RLCT extraction, termination, transition invariant, automatic
  Case 2 gap/tail transport, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-source-terminal-product-candidate-a4.md`.
- Review artifact:
  `review-case2-source-terminal-product-candidate-a4.md`.

## Verification

- From `lean/`: `lake build DLNFibre.DLN.Aoyagi.EntryIdeal`
- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `./scripts/sorries`
