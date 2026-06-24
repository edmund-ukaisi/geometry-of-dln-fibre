# Statement card - A6 Definition 3 positive-remainder ceiling data

Date: 2026-06-24.

## Claim

If a selected-width family has a supplied positive-remainder decomposition

```text
sum_j m_j = ell * ceilPred + a,        0 < a <= ell,
```

then it determines an `AoyagiDefinition3CeilData` with

```text
ceilWidth = ceilPred + 1,
aParam = a.
```

## Source Status

Aoyagi Definition 3 on PDF pp. 8-9 defines the ceiling integer `M` by
`M - 1 < T/ell <= M` and sets `a = T - (M - 1)ell`, where `T` is the selected
reduced-width sum.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-positive-remainder-ceil-data-a6.md`.

Review:
`review-definition3-positive-remainder-ceil-data-a6.md`.

Verdict: pass.

## Lean Status

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

```text
AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder
```

This is pure finite arithmetic on supplied selected-width data.

## Nonclaims

No source-facing wrapper is added in this slice, and no selected-cutpoint
existence, Definition 3 classification, uniqueness theorem, Eq5 payload,
chart production, normal crossings, pole order, or RLCT extraction is proved.
