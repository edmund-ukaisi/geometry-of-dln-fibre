# Statement card - A6 Definition 3 equal-width source data

Date: 2026-06-24.

## Claim

In Aoyagi's equal-width example, where every source-range reduced width is a
positive constant `w`, Definition 3 source data exists by taking `ell = L` and
all consecutive source layers as selected cutpoints.

## Source Status

Aoyagi Definition 3 and the equal-width example on PDF pp. 8-9 support the
choice `ell = L` when

```text
M^(1) = M^(2) = ... = M^(L+1).
```

This is an Aoyagi-only source claim and does not use the quiver-based paper.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-equal-width-source-data-a6.md`.

Review:
`review-definition3-equal-width-source-data-a6.md`.

Verdict: pass for the narrow equal-width constructor.  Required hypotheses are
`0 < L`, `0 < w`, and constancy on the full source range `1 <= s <= L+1`.

## Lean Status

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

```text
AoyagiDefinition3SourceData.exists_consecutive_of_constant_reducedWidth_pos
```

The theorem constructs `C : AoyagiSelectedCutpoints L` with

```text
C.cut j = j.val + 1
```

and proves `AoyagiDefinition3SourceData L L H r C` from the positive constant
reduced-width hypothesis.

## Nonclaims

This is not arbitrary selected-cutpoint existence, not an `ell > 1`
classification, not a repair of Definition 3's printed inequalities, not Eq5
construction or Lemma 5 exactness, and not chart production, normal crossings,
pole order, or RLCT extraction.
