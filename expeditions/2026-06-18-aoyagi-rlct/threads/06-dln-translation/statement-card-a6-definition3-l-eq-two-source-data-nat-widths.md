# Statement Card - A6 Definition 3 `L=2` Source-Data Nat Widths

Date: 2026-07-02.

## Claim

For `L=2`, supplied Definition 3 source-data existence implies source-range
rank-width and therefore produces natural witnesses `w1,w2,w3` for the three
source-range reduced widths.  The existing branch-disjunction theorem can
therefore be restated without asking for those Nat-width identities as inputs.

## Source Status

Aoyagi Definition 3 on PDF pp. 8-9 supplies the source-data inequalities.  The
result uses the already-formalized `L=2` finite classification into
repeated-positive and triangle branches.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-l-eq-two-source-data-nat-widths-a6.md`.

Review:
`review-definition3-l-eq-two-source-data-nat-widths-a6.md`.

## Lean Target

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

Lean names:

```text
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_L_eq_two_sourceData
AoyagiDefinition3SourceData.exists_reducedWidthNatTriple_of_L_eq_two_sourceData
AoyagiDefinition3SourceData.exists_L_eq_two_theorem2Formula_branchDisjunction_of_sourceData_natWidths
```

## Nonclaims

No generalization to `L > 2`, no canonical branch choice, no branch-independent
lambda/order payload, no Eq5 payload, no chart production, no normal crossings,
and no analytic pole-order/RLCT extraction.
