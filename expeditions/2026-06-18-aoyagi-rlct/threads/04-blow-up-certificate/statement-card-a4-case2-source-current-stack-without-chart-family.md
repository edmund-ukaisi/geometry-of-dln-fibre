# Statement card - A4 source-current stack without chart family

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withoutChartFamily`
- existing `sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withCorrectedPostData` as a compatibility wrapper

## Claim

The continuing Case 2 source-current row stack wrapper can be constructed
without a supplied `Case2ResidualBlockChartFamilyBoundary`.  It rewrites the
chart-family-free old-top/source-suffix paper-`C'` stack through the existing
source-current row equivalence.

## Inputs Kept Explicit

- `1 <= S`, `S <= L`;
- the continuation guard `J+1 <= prefixMinNat n (S+1)`;
- the continuing guard `J+2 <= prefixMinNat n (S+1)`;
- old exponent certificates, level/least-value bridge, and integer
  least-value gap;
- the displayed chart variables `u`, `residual`, and source following factor
  `C`;
- the supplied suffix index family `κ`, tail matrices `Ctail`, and
  `hSuffix : S+1 <= L`.

## Proved

The new direct constructor fills the same finite source-current row stack
conclusion as the older chart-family-bearing API, but without `ChartRegular`,
`TransitionRegular`, or `Case2ResidualBlockChartFamilyBoundary` arguments.
The older API remains available and delegates to the direct constructor.

## Not Proved

No chart-produced successor following object, no source-produced
`C'^(S+1)`, no suffix production or inheritance, no successor chart family,
no coverage or transition regularity, no coordinate-derived corrected
post-data, no analytic Jacobian/volume-form theorem, no normal-crossing
certificate, no pole order, no termination theorem, no RLCT extraction, and no
repair of the printed Case 2 vector mismatch.

## Verification

Controller ran:

```text
cd lean && LAKE_JOBS=1 lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && scripts/sorries
git diff --check
```

The focused Lake target passed.  The no-sorry scanner reported `0 sorry`,
`0 #exit`, `0 native_decide`, and `0 axiom`.  `git diff --check` passed.

## Review

Xhigh source/fidelity audit and xhigh Lean dependency audit passed.  See
`review-case2-source-current-stack-without-chart-family-a4.md`.
