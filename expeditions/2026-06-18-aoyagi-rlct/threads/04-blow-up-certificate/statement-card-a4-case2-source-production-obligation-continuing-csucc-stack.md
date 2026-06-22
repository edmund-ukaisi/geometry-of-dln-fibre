# Statement Card - A4 Case 2 Source-Production Obligation Continuing Csucc Stack

## Lean Names

```text
Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_Csucc_currentFollowingBlock_eq_formula
Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_sourceCurrentStack_suppliedCsucc
```

## Claim

Given a supplied Case 2 `SourceProductionObligation`, the current source-row
block of its supplied successor following factor `Csucc` is the existing
formula-level successor block.  Under the continuing-branch hypothesis
`J+2 <= prefixMinNat n (S+1)`, the existing old-top/source-suffix continuing
stack identity can therefore be stated with
`case2SourceCurrentFollowingBlock n S Csucc` on the successor side.

## Inputs Kept Explicit

- the displayed supplied chart-family boundary `data`;
- the source suffix bound `S+1 <= L`;
- finite source row/column types `κ` with `Fintype` and `DecidableEq`;
- the source following factor `C`, suffix factors `Ctail`, supplied `Csucc`,
  and supplied `Cterm`;
- the supplied obligation
  `SourceProductionObligation data residual κ hSuffix C Ctail Csucc Cterm`;
- the continuing branch guard `J+2 <= prefixMinNat n (S+1)`.

## Proved

Only finite row-block rewriting:

```text
case2SourceCurrentFollowingBlock n S Csucc
  =
case2SourceSuccessorFollowingBlock n hS hcont residual C
```

and the corresponding source-current stack payload with the actual source
suffix.

## Not Proved

No construction of the obligation, `Csucc`, `C'^(S+1)`, a source suffix, a
successor chart family, chart coverage, transition regularity, coordinate
post-data, Jacobian arithmetic, normal crossings, pole order, termination,
RLCT, or repair of the printed Case 2 vector mismatch.
