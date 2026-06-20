# Statement card - A4 Case 2 source old-top/suffix specialization

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2SourceOldTopRowIndex`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceOldTopWeight`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceOldTopBlock`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedOldTopSuffixTerminalProduct_entryIdeal_eq_of_not_next_cont`

## Statement

Lean now specializes the stopped displayed Case 2 terminal theorem to old top
source rows `1,...,J`.  The old top multiplier is

```text
diag(pre.weight i), i=1,...,J,
```

and the old top block is the source row restriction

```text
C(i,t), i=1,...,J.
```

The suffix `F` remains a supplied matrix parameter.

## Proved

- The arbitrary old-top multiplier and old-top block in the terminal-product
  theorem can be instantiated by source-shaped old-top data.
- The same stopped terminal entry-ideal equality follows by specialization of
  the existing supplied theorem.

## Assumed

- A displayed Case 2 supplied chart-family boundary.
- Failed next continuation `not (J+2 <= prefixMinNat n (S+1))`.
- Source-coordinate residual and following data.
- A supplied suffix matrix `F`.

## Not Proved

- No construction of the suffix product `prod_{s=S+2}^L C^(s)`.
- No proof that the resulting stack is source-produced `C'^(S+1)`.
- No chart-produced recurrence/exponent data.
- No chart coverage or regularity, Jacobian arithmetic, normal crossings,
  RLCT extraction, termination, transition invariant, automatic Case 2 gap/tail
  transport, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-source-old-top-suffix-specialization-a4.md`.
- Review artifact:
  `review-case2-source-old-top-suffix-specialization-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
