# Statement card - A4 Case 2 displayed terminal source model

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalWeightCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalCnextCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalProductCandidate`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.not_next_cont_of_actualWidth_exhausted`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.introducedLabel_terminal_iff_succStage_zero`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedActualWidthTerminalSourceModel.introducedLabelFinset_terminal_eq_succStage_zero`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_weightedTerminalProduct_entryIdeal_eq_terminalProductCandidate_of_actualWidth`

## Statement

Lean now packages the actual-width-exhausted displayed Case 2 terminal branch
as a supplied source-order model.  The model carries supplied old top data
`Atop`, `Ctop`, a supplied suffix `F`, and the hypothesis

```text
n(S+1) = J+1.
```

It names the supplied candidate product

```text
(blockdiag(Atop, [b0]) * [Ctop; C0]) * F,
```

where `C0` is the top pivot row of `C' = Q^-1 C`.  Under a supplied displayed
Case 2 boundary, with `b0 = post.weight (J+1)`, the source-chart product has
the same matrix-entry ideal as this model's terminal product.

## Proved

- Actual next-width exhaustion implies failed next continuation.
- Actual next-width exhaustion identifies the introduced-label finite domain
  at old `(S,J+1)` with the domain at stage-relabelled `(S+1,0)`.
- The supplied model's terminal product unfolds to the existing source-order
  candidate product.
- The supplied displayed-boundary entry-ideal theorem applies with the
  model-derived failed-continuation proof.

## Assumed

- A supplied `Case2DisplayedSuppliedChartFamilyBoundary`.
- Supplied old top multiplier `Atop`, old top block `Ctop`, and suffix `F`.
- Actual next-width exhaustion `n(S+1)=J+1`.
- Finite row/column types needed for matrix multiplication.

## Not Proved

- No proof that `Atop`, `Ctop`, or `F` are chart-produced source objects.
- No proof that `[Ctop;C0]` is Aoyagi's source-produced `C'^(S+1)`.
- No construction of recurrence or exponent post-data over `(S+1,0)`.
- No chart production, chart coverage or regularity, Jacobian arithmetic,
  normal crossings, RLCT extraction, termination, transition invariant, or
  printed-vector repair.
- The row-prefix-exhausted terminal branch is not covered unless actual
  next-width exhaustion also holds.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-terminal-source-model-a4.md`.
- Review artifact:
  `review-case2-displayed-terminal-source-model-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
