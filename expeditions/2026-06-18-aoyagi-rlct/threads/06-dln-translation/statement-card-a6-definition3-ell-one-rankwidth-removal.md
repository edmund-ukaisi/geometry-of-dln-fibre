# Statement Card - A6 Definition 3 `ell=1` Rank-Width Removal

Date: 2026-07-02.

## Claim

For a supplied

```text
S : AoyagiDefinition3SourceData L 1 H r C,
```

Definition 3's own `ell=1` inequalities imply source-range rank-width:

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

Consequently the existing `ell=1` finite Theorem 2 source-data formula can be
restated without a separate rank-width input.

## Source Status

Aoyagi Definition 3 on PDF pp. 8-9 supplies the selected/nonselected
reduced-width inequalities.  The argument uses the `ell=1` specialization:
strict selected inequalities make both selected values positive, and the
nonselected upper inequality has coefficient `0`.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-ell-one-source-data-rankwidth-removal-a6.md`.

Review:
`review-definition3-ell-one-rankwidth-removal-a6.md`.

## Lean Target

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

Lean names:

```text
AoyagiDefinition3SourceData.sourceRangeRankWidth_of_ell_eq_one
AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_sourceData_general
```

## Nonclaims

No branch selection, no canonical selected pair, no branch-independent formula
payload, no Eq5 payload, no chart production, no normal crossings, and no
RLCT extraction.  The finite displayed order formula is returned; no analytic
pole-order/RLCT identification is proved.
