# Statement card - A4 Case 2 displayed source-terminal candidate

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalWeight`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalCnext`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalCprimeCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalCprimeCandidate_eq_weight_mul_cnext_mul`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalCprimeCandidate_eq_verticalBlock_mul`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedWeightedTerminalProduct_entryIdeal_eq_topStack_of_not_next_cont`

## Statement

Lean now names the source-order candidate terminal product

```text
(blockdiag(Wold, [b0]) * [Cold; C0]) * F,
```

where `C0` is the top pivot row of `C' = Q^-1 C`, and proves a displayed
Case 2 supplied-boundary wrapper.  Given supplied old top multiplier `Atop`,
supplied old top block `Ctop`, supplied remaining suffix `F`, and failed next
continuation, the source-chart `Q/P` product from the supplied displayed
boundary has the same matrix-entry ideal as this candidate terminal product
with `b0 = post.weight (J+1)`.

## Proved

- The candidate terminal product is named with weights outside the unweighted
  stack `[Cold; C0]`.
- The terminal weight matrix and unweighted `Cnext` stack are named
  separately.
- The displayed supplied source-chart `Q/P` identity can be lifted through an
  unchanged supplied old top block and suffix.
- After failed next continuation, the weighted stopped terminal absorption
  rewrites the matrix-entry ideal to the named source-order candidate product.
- The residual row weights on the terminal side are the supplied successor
  recurrence weights from `post`.

## Assumed

- A supplied `Case2DisplayedSuppliedChartFamilyBoundary`.
- Displayed pivot validity and failed next continuation.
- Supplied old top multiplier `Atop`, old top block `Ctop`, and remaining
  following product `F`.
- Finite row/column types needed for matrix multiplication.

## Not Proved

- No proof that `Atop`, `Ctop`, or `F` are Aoyagi's source-produced old
  diagonal weights, old top rows, or remaining product.
- No proof that `[Ctop; C0]` is Aoyagi's actual `C'^(S+1)`.
- No row-vs-column terminal branch theorem beyond the displayed pivot-first
  stopped block already available.
- No chart production, chart coverage or regularity, Jacobian arithmetic,
  normal crossings, RLCT extraction, termination, transition invariant, or
  printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-source-terminal-candidate-a4.md`.
- Review artifact:
  `review-case2-displayed-source-terminal-candidate-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
