# Statement card - A4 Case 2 Source Current Stack

## Lean Name

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withCorrectedPostData`

## Claim

The continuing Case 2 old-top/source-suffix stack identity can be restated
with source-current row blocks.  The old following side uses
`case2SourceCurrentFollowingBlock`, and the transported side uses
`case2SourceSuccessorFollowingBlock`, both reindexed by the finite source-row
equivalence.

## Proved

Lean proves the source-current-row stack equality by rewriting the existing
pivot-first stack equality through the two source-current row-reindexing
identities.  The theorem preserves the previous next-center nonemptiness,
corrected exponent-domain data, post level/gap data, and finite center
principalization outputs.

## Assumed

The same hypotheses as the previous continuing old-top/source-suffix stack:
stage and suffix bounds, displayed continuation and next-continuation
hypotheses, supplied recurrence state/post-data boundary, corrected exponent
pre-data, level/gap data, chart-family boundary, source following factor, and
raw source suffix.

## Deferred

Chart production of the successor following factor, source production of
`C'^(S+1)`, source-suffix production, recurrence/exponent post-data
production from coordinates, transition invariance, Jacobian arithmetic,
normal crossings, pole order, termination, and RLCT extraction.

## Cited

None; this is finite row-index and matrix-definition bookkeeping.

## Verification

Focused Lean checks and full library checks pass:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

## Review

PASS.  Independent xhigh review found no required fixes; see
`review-case2-source-current-stack-a4.md`.
