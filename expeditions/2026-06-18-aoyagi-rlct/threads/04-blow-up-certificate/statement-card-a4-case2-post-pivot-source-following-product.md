# Statement card - A4 Case 2 post-pivot source-following product

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct_sourceFollowingFactor`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.postPivotNextSameStageProduct_sourceFollowingFactor`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_postPivotNextSameStageProduct_withSourceFollowingFactorAndCorrectedPostData`

## Statement

Lean now rewrites the continuing displayed Case 2 lower-row product directly
with the next same-stage source following factor:

```text
(D''' * C')_tail =
  case2DisplayedPostPivotResidualBlock n hS hcont residual *
    case2SourceFollowingFactor (n := n) (S := S) (J := J+1) C.
```

The theorem combines the post-pivot next-block adapter with the tail identity
for `C' = Q^-1 C`.  Boundary and concrete source-chart package projections are
also exposed.

## Proved

- The raw lower-row product of Aoyagi's displayed `D''' * C'`, reindexed to
  `(S,J+1)` rows, equals the supplied post-pivot residual block times
  `case2SourceFollowingFactor (J := J+1) C`.
- Any supplied displayed Case 2 boundary exports this same source-following
  product identity.
- The concrete displayed source-chart constructor packages this product
  identity with the corrected supplied post-data projections.

## Assumed

- Displayed Case 2 stage and continuation hypotheses: `1 <= S`,
  `S <= L`, and `J+1 <= prefixMinNat n (S+1)` where applicable.
- The concrete package uses the existing supplied chart-family boundary and
  corrected selected-label post-data constructor.

## Cited

- None in Lean.  This is finite matrix algebra and reindexing.

## Deferred

- Chart production of recurrence or exponent post-data.
- Construction of a successor chart-family boundary for `(S,J+1)`.
- Identification with a full source-produced next `C'^(S+1)`.
- Atlas coverage, arbitrary pivot coverage, coordinate regularity,
  transition invariance, Jacobian arithmetic, normal crossings, RLCT
  extraction, terminal relabeling, and printed-vector repair.

## Review

- Source/math obstruction audit by xhigh `Kant`.
- Lean/API target audit by xhigh `Bernoulli`.
- Landed-patch review passed by xhigh `Aquinas`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
