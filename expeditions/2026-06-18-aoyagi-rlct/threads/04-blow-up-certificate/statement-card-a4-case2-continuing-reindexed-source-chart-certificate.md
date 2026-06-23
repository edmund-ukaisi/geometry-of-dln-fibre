# Statement card - A4 Case 2 continuing reindexed source-chart certificate

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `Case2DisplayedReindexedNextSourceProductEq`
- `Case2DisplayedContinuingReindexedSourceChartCertificate`
- `sourceChartMap_continuingReindexedSourceChartCertificate`

## Claim

The displayed continuing Case 2 source chart has a non-vacuous local
certificate that packages:

- the concrete displayed selected-entry source chart;
- finite center membership, divisibility, and principalization;
- nonempty next residual center under `J+2 <= prefixMinNat n (S+1)`;
- the reindexed next same-stage source-product identity;
- corrected exponent, level, least-value-gap, recurrence-gap, and numerator
  count post-data.

## Inputs Kept Explicit

- `1 <= S`, `S <= L`;
- `J+1 <= prefixMinNat n (S+1)`;
- `J+2 <= prefixMinNat n (S+1)` for next-center nonemptiness;
- pre-state exponent/level/gap hypotheses;
- the supplied current residual-block chart-family boundary;
- source residual coordinates and following factor `C`.

## Proved

The constructor proves:

```text
case2DisplayedSourceChartMap(J+1,J+1) = u,
p != (J+1,J+1) -> chartMap(p) = u * residual(p),
span(transformed center values) = span({u}),
post.weight i = upivot * pre.weight i for J+1 <= i,
new numerator = card(case2ResidualBlockPivotEntries n S J),
```

and packages the displayed source-chart `Q/P` identity after finite reindexing
to the next `(S,J+1)` source-product shape.

## Not Proved

No source production of `Csucc`, no source suffix or terminal source
production, no successor chart-family construction, no chart coverage, no
transition regularity, no Jacobian arithmetic, no unit nonvanishing, no loss
monomial identity, no normal crossings, no pole order, no RLCT extraction.

The corrected post-weight convention is used; this is not a literal
double-counting of Aoyagi's printed outside `u` factor.

## Verification

Focused Lean check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```

## Review

Xhigh source reviewer `Einstein the 2nd` passed the slice and confirmed that
it stays A4-local.  Xhigh Lean/API reviewer `Popper the 2nd` passed the slice;
the only residual risk is proof brittleness from abbreviating a long matrix
equality and unfolding it by `simpa`.

Durable review artifact:
`review-case2-continuing-reindexed-source-chart-certificate-a4.md`.
