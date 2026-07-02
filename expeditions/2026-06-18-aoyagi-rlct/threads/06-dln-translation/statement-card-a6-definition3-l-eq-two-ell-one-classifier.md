# Statement Card - A6 Definition 3 `L=2`, `ell=1` Classifier

Date: 2026-07-02.

## Claim

For `L=2`, existence of Definition 3 source data with `ell=1` is equivalent
to positivity of the three source-range reduced widths plus repetition among
those three values.

## Source Status

Aoyagi Definition 3 on PDF pp. 8-9 supplies the finite selected and
nonselected inequalities.  The proof uses only the already-formalized
`ell=1` cover lemma and the existing repeated-positive constructor.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-l-eq-two-ell-one-classifier-a6.md`.

Review:
`review-definition3-l-eq-two-ell-one-classifier-a6.md`.

## Lean Target

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

Lean name:

```text
AoyagiDefinition3SourceData.exists_ell_one_sourceData_iff_repeatedPositive_of_L_eq_two
```

The complete `L=2` source-data classifier now uses this theorem for its
`ell=1` forward case.

## Nonclaims

No generalization to `L > 2`, no arbitrary-`ell` classifier, no canonical
branch choice, no branch-independent lambda/order payload, no Eq5 payload, no
chart production, no normal crossings, and no analytic pole-order/RLCT
extraction.
