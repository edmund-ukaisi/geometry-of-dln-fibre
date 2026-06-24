# Statement card - A4 Case 2 weighted source-residual successor following product

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2WeightedDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_succFollowing`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_weightedLowerRows_sourceResidualSucc_withCorrectedPostData`

## Statement

The lower rows of the weighted displayed Case 2 product
`(diag(b0,b) * D''') * C'` can be written in source-coordinate notation as

```text
diag(b_tail) *
  (case2SourceResidualBlock(postPivotSourceResidual)
    *
   case2SourceFollowingFactor(S,J+1,Csucc)).
```

The displayed source-chart handoff carries the same identity with the
successor recurrence weight diagonal and the already proved corrected
exponent, level, least-value-gap, and recurrence-gap post-data.

## Proved

The proof combines:

- the existing weighted lower-row theorem for a free pivot-first `C'`;
- the paper-specific tail equality for `C' = Q^-1 C`;
- the source residual representative equality;
- the fact that the `(S,J+1)` following-factor restriction ignores the
  replaced row `J+1` of the formula-level successor following factor.

## Assumed

- Displayed Case 2 hypotheses `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`.
- Source residual data and a following factor `C`.
- For the source-chart handoff: the existing displayed chart-family boundary
  assumptions needed by the older corrected-post-data theorem.

## Cited

- None in Lean.  This is finite matrix reindexing and source-coordinate
  notation rewriting.

## Deferred

- Pivot-row product, old top rows, suffix product, source production of
  `postPivotSourceResidual` or `Csucc`, a full successor `C'^(S+1)`, chart
  coverage, transition invariance, analytic Jacobian/volume control,
  normal-crossing certificate production, pole order, termination, and RLCT
  extraction.

## Review

- xhigh reviewer `Lovelace` passed the slice with no blocking findings.

## Verification

- `lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `lean/scripts/lb DLNFibre` passed.
- `lean/scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
