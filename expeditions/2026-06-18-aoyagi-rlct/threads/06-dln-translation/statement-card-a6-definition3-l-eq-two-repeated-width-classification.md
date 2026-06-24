# Statement card - A6 Definition 3 `L=2` repeated-width classification

Date: 2026-06-24.

## Claim

For `L=2`, Definition 3 source data exists exactly when either:

- all three source-range reduced widths are positive and at least two of them
  are equal; or
- the three all-source triangle inequalities hold:

```text
2*w1 < w1+w2+w3,
2*w2 < w1+w2+w3,
2*w3 < w1+w2+w3.
```

## Source Status

Aoyagi Definition 3 on PDF pp. 8-9 supplies selected cutpoints and imposes
value-level selected/nonselected conditions.  The repeated-width branch uses
the fact that an unchosen source position with a selected reduced-width value
is not nonselected.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-l-eq-two-repeated-width-classification-a6.md`.

Review:
`review-definition3-l-eq-two-repeated-width-classification-a6.md`.

Verdict: pass.

## Lean Status

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

```text
AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one
AoyagiDefinition3SourceData.of_ell_eq_one_selectedValueSet_covers
AoyagiDefinition3SourceData.exists_ell_one_of_L_eq_two_positive_repeated
AoyagiDefinition3SourceData.exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two
```

The old rank-width version
`reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth` remains as a
compatibility wrapper.

## Nonclaims

No classification for `L>2`, no source production from concrete matrix data,
no ceiling-data package, no Eq5 payload, no chart production, no normal
crossings, no pole order, and no RLCT extraction.
