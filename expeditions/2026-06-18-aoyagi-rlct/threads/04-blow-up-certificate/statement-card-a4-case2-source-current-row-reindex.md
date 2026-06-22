# Statement card - A4 Case 2 Source Current Row Reindex

## Lean Names

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2SourceCurrentRowIndex`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2SourceOldTopPaperCprimeRowEquiv`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2SourceCurrentFollowingBlock`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2SourceSuccessorFollowingBlock`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2SourceCurrentFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2SourceSuccessorFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv`

## Claim

The old top rows, the displayed pivot row, and the pivot-complement rows of
Aoyagi's continuing Case 2 following factor reindex to the single source row
interval `1..n(S+1)`.  Under this reindexing, the old following block is
`[oldTop; displayedSourceFollowingFactor]`, and the formula-level successor
following block is `[oldTop; paperCprime]`.

## Proved

Lean proves the finite row equivalence and the two matrix reindexing
identities.  The proof uses only interval membership, the displayed
continuation bound, and the existing definitions of
`case2DisplayedSourceSuccessorFollowingFactor`,
`case2DisplayedSourceFollowingFactor`, and `case2DisplayedPaperCprime`.

## Assumed

The stage positivity hypothesis `1 <= S` and the displayed continuation bound
`J+1 <= prefixMinNat n (S+1)`.  The matrix entries themselves are arbitrary
source-coordinate functions and residual data.

## Deferred

Chart production of the successor following factor, source production of
`C'^(S+1)`, source-suffix production, recurrence/exponent post-data
production, transition invariance, Jacobian arithmetic, normal crossings, pole
order, termination, and RLCT extraction.

## Cited

None; this is finite index and matrix-definition bookkeeping.

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

xhigh review passed after namespace metadata repair.  Review artifact:
`review-case2-source-current-row-reindex-a4.md`.
