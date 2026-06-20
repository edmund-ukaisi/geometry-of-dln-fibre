# Statement card - A4 Case 2 displayed weighted terminal product

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`
- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.sumElim_mul`
- `DLNFibre.DLN.Aoyagi.matrixEntryIdeal_sumElim_zero_bottom_mul`
- `DLNFibre.DLN.Aoyagi.matrixEntryIdeal_sumElim_congr_bottom_mul`
- `DLNFibre.DLN.Aoyagi.matrixEntryIdeal_case2DisplayedPaperWeightedTerminalProduct_eq_topStack_of_not_next_cont`

## Statement

Lean proves a displayed Case 2 weighted terminal-product absorption theorem.
Given supplied old top data `Wold`, `Cold`, supplied residual weights
`b0`, `b`, and a supplied remaining following product `F`, failed next
continuation gives

```text
matrixEntryIdeal
  ((blockdiag(Wold, weightedPivotDiagonal b0 b)
      * [Cold; D''' * C']) * F)
=
matrixEntryIdeal
  [ (Wold * Cold) * F ; (b0 * C0) * F ],
```

where `C0` is the top pivot row of `C' = Q^-1 C`.

## Proved

- Right multiplication distributes over a stacked row block.
- A zero bottom row block remains entry-ideal invisible after a common right
  multiplication.
- Replacing the lower row block by another whose product with the same right
  factor has the same entry ideal preserves the stacked product entry ideal.
- In displayed Case 2 under failed next continuation, the diagonal-weighted
  terminal product with a supplied suffix `F` has the same matrix-entry ideal
  as the stack of the old weighted top product and the surviving weighted
  pivot row product.

## Assumed

- Displayed pivot validity and failed next continuation.
- Supplied old top block `Cold`, old top row-weight matrix `Wold`, residual
  weights `b0`, `b`, and remaining following product `F`.
- Finite row/column types needed for matrix multiplication.

## Not Proved

- No proof that `Cold`, `Wold`, or `F` are the source's actual old top rows,
  old diagonal weights, or remaining product.
- No construction or identification of Aoyagi's next-stage `C'^(S+1)`.
- No row-vs-column source terminal presentation.
- No chart-produced recurrence or exponent post-data.
- No chart coverage, coordinate regularity, Jacobian/volume arithmetic,
  normal crossings, RLCT extraction, termination theorem, transition
  invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-weighted-terminal-product-a4.md`.
- Review artifact:
  `review-case2-displayed-weighted-terminal-product-a4.md`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.EntryIdeal`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
