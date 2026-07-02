# Statement Card - A6 `L=2`, `ell=1` Repeated Formula Branch

Date: 2026-07-02.

## Claim

For supplied `L=2`, `ell=1` Definition 3 source data, the finite Theorem 2
formula dispatch lands in the repeated-positive branch package.

## Source Status

Aoyagi Definition 3 on PDF pp. 8-9 supplies the finite source-data
inequalities.  The proof uses the extracted fixed-`ell=1` classifier and the
already-formalized repeated-positive formula package.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-l-eq-two-ell-one-source-data-repeated-formula-branch-a6.md`.

## Lean Target

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

Lean names:

```text
AoyagiDefinition3SourceData.exists_L_eq_two_ell_one_theorem2Formula_repeatedBranch_of_sourceData
AoyagiDefinition3SourceData.exists_L_eq_two_ell_one_theorem2Formula_repeatedBranch_of_sourceData_natWidths
```

## Nonclaims

No arbitrary-`ell` branch choice, no branch-independent lambda/order payload,
no Eq5 payload, no chart production, no normal crossings, and no analytic
pole-order/RLCT extraction.
