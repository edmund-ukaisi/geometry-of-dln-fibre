# Statement card - A4 direct Case 2 reindexed next-source product

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData`
- `sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData`
  as a compatibility wrapper

## Claim

For Aoyagi's displayed Case 2 pivot `(J+1,J+1)`, the reindexed next
same-stage source-product identity and the corrected concrete `case2Succ`
post-data follow directly from the old exponent data, level bridge,
least-value gap, the displayed source chart map, the concrete successor
recurrence post-data, and the low-level finite `Q/P` identity.  A supplied
`Case2ResidualBlockChartFamilyBoundary` is not needed for this finite theorem.

## Inputs Kept Explicit

- `1 <= S`, `S <= L`, and `J+1 <= prefixMinNat n (S+1)`;
- the pre-state recurrence data `pre`;
- the displayed chart variables `u` and `residual`;
- the old introduced-label exponent certificates;
- the old level/least-value bridge;
- the old integer Case 2 least-value gap;
- the following factor `C`.

## Proved

The direct theorem supplies a row-operation witness `q` and proves
`Case2DisplayedReindexedNextSourceProductEq` in expanded form: the displayed
source-chart substituted product, after reindexing the old top rows, pivot row,
and post-pivot residual rows, is the next same-stage source product with the
formula-level successor following factor
`case2DisplayedSourceSuccessorFollowingFactor`.

It also proves the corrected post-data fields for the concrete successor
`pre.case2Succ upivot`:

- extended introduced-label exponent certificates at `(S,J+1)`;
- level/least-value invariants at `(S,J+1)`;
- the successor integer Case 2 least-value gap;
- the successor recurrence Case 2 gap.

The existing chart-family-bearing theorem is retained only as a compatibility
wrapper and should delegate to the direct theorem.

## Not Proved

No source production of `Csucc`, no successor chart family, no suffix
production, no coverage or transition regularity, no analytic
Jacobian/volume-form theorem, no normal-crossing certificate, no pole order,
and no RLCT extraction.

## Verification

Controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

The focused raw Lean check, focused Lake target, full aggregator build, no-sorry
check, and diff hygiene check passed.  The full aggregator build emitted only
unrelated pre-existing Core linter warnings.

## Review

Xhigh fidelity/bedrock review passed.  See
`review-case2-reindexed-next-source-product-direct-a4.md`.
