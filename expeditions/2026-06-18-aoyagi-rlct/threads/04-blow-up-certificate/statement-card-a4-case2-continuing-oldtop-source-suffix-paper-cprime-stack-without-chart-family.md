# Statement card - A4 continuing old-top/source-suffix paper-Cprime stack without chart family

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily`
- existing `sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData` as a compatibility wrapper

## Claim

The continuing Case 2 old-top/source-suffix stack identity with paper
`C' = Q^-1 C` can be constructed without a supplied
`Case2ResidualBlockChartFamilyBoundary`.  Its proof uses finite `Q/P` algebra,
concrete `case2Succ` recurrence data, corrected selected-label exponent
post-data, old-top row lifting, and right multiplication by the supplied raw
source suffix.

## Inputs Kept Explicit

- `1 <= S`, `S <= L`;
- the continuation guard `J+1 <= prefixMinNat n (S+1)`;
- the continuing guard `J+2 <= prefixMinNat n (S+1)`;
- old exponent certificates, level/least-value bridge, and integer
  least-value gap;
- the displayed chart variables `u`, `residual`, and following factor `C`;
- the supplied suffix index family `κ`, tail matrices `Ctail`, and
  `hSuffix : S+1 <= L`.

## Proved

The new direct constructor fills the same finite old-top/source-suffix stack
conclusion without `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` arguments.  The older constructor
remains available but delegates to the direct constructor.

## Not Proved

No source production of `Csucc`, no source-produced `C'^(S+1)`, no suffix
production, no successor chart family, no coverage or transition regularity,
no analytic Jacobian/volume-form theorem, no normal-crossing certificate, no
pole order, no RLCT extraction, and no repair of the printed Case 2 vector
mismatch.

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

Xhigh source/reproduction audit and xhigh Lean dependency audit passed.  See
`review-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family-a4.md`.
