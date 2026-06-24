# Statement card - A6 Definition 3 `ell=1` source-data formula

Date: 2026-06-24.

## Claim

For a supplied

```text
S : AoyagiDefinition3SourceData L 1 H r C
```

and source-range rank-width, Lean can derive the finite Theorem 2 formula data
for the two selected widths

```text
u = H(C.cut 0) - r,
v = H(C.cut 1) - r.
```

This removes the need to separately pass selected-value cover, selected
positivity, selected value equalities, and cutpoint bounds to the existing
general `ell=1` formula theorem.

## Source Status

Aoyagi Definition 3 on PDF pp. 8-9 supplies the `ell=1` strict selected
inequalities and value-level selected set clauses.  The result assumes
`ell=1`; it does not choose a branch.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-ell-one-source-data-formula-a6.md`.

Review:
`review-definition3-ell-one-source-data-formula-a6.md`.

## Lean Status

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

Lean name:

```text
AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_sourceData_rankWidth_general
```

Focused elaboration passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

## Nonclaims

No branch selection, no canonical selected pair, no branch-independent formula
payload, no source-rank/final-socket wrapper, no Eq5 payload, no chart
production, no normal crossings, no pole order, and no RLCT extraction.
