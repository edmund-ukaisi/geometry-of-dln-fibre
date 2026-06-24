# Statement card - A6 Definition 3 all-source strict rank-width

Date: 2026-06-24.

## Claim

In the all-source branch of Aoyagi Definition 3, the strict selected
inequalities

```text
L * M^(s) < sum_j M^(j)
```

for every source index already imply `r <= H(s)` for every source index.
Consequently the all-source selected ceiling-data package can drop its
separate rank-width hypothesis.

## Source Status

Aoyagi Definition 3 on PDF pp. 8-9 supplies the strict selected inequalities.
The theorem is only for the explicit all-source branch `ell=L`,
`C.cut j=j+1`; it does not choose between overlapping branches.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-all-source-strict-rank-width-a6.md`.

Review:
`review-definition3-all-source-strict-rank-width-a6.md`.

## Lean Status

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

Lean names:

```text
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_all_selected_strict
AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict
```

Focused check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

## Nonclaims

No arbitrary Definition 3 existence, no classification beyond the all-source
branch, no closed form for `ceilWidth` or `aParam`, no Eq5 construction, no
chart production, no normal crossings, no pole order, and no RLCT extraction.
