# Statement card - A4 paper-Cprime lower rows without chart family

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `sourceChartMap_paperCprimeWeightedLowerRows_withoutChartFamily`
- `sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withoutChartFamily`
- existing `sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData` as a compatibility wrapper
- existing `sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withCorrectedPostData` as a compatibility wrapper

## Claim

The continuing Case 2 lower-row paper-`C'` handoff, and its right-multiplied
following-product variant, can be constructed without a supplied
`Case2ResidualBlockChartFamilyBoundary`.  The proof uses finite displayed
`Q/P` algebra, concrete `case2Succ` recurrence data, corrected selected-label
exponent post-data, lower-row projection, and the paper-`C'` lower-tail
identity.

## Inputs Kept Explicit

- `1 <= S` and `S <= L`;
- the continuation guard `J+1 <= prefixMinNat n (S+1)`;
- old exponent certificates, level/least-value bridge, and integer
  least-value gap;
- the displayed chart variables `u`, `residual`, and source following factor
  `C`;
- in the second theorem, the supplied right factor `F`.

## Proved

The two new direct constructors fill the same finite lower-row conclusions as
the older chart-family-bearing APIs, but without `ChartRegular`,
`TransitionRegular`, or `Case2ResidualBlockChartFamilyBoundary` arguments.
The older APIs remain available and delegate to the direct constructors.

## Not Proved

No pivot-row equality, no source production of `Csucc`, no source-produced
`C'^(S+1)`, no suffix production, no successor chart family, no coverage or
transition regularity, no analytic Jacobian/volume-form theorem, no
normal-crossing certificate, no pole order, no RLCT extraction, and no repair
of the printed Case 2 vector mismatch.

## Verification

Controller ran:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && scripts/sorries
git diff --check
```

The focused Lake target passed.  The no-sorry scanner reported `0 sorry`,
`0 #exit`, `0 native_decide`, and `0 axiom`.  `git diff --check` passed.

## Review

Xhigh source-production frontier audit and xhigh Lean dependency audit passed.
See `review-case2-paper-cprime-lower-rows-without-chart-family-a4.md`.
