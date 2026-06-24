# Statement card - A6 Definition 3 `L=2` branch formula disagreement

Date: 2026-06-24.

## Lean declaration

File:
`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`

New theorem:

```text
AoyagiDefinition3SourceData.exists_L_eq_two_two_three_three_formula_disagreement
```

## Statement

For the concrete reduced-width profile

```text
L = 2,  r = 0,  (M^(1), M^(2), M^(3)) = (2,3,3),
```

the currently formalised printed Definition 3 conditions admit both:

- an `ell=1` repeated-positive source-data choice, selecting values `(2,3)`;
- an `ell=2` all-source triangle source-data choice, selecting `(2,3,3)`.

The theorem constructs both packages and proves their finite Theorem 2 lambda
formula values differ:

```text
lambda_ell1 = 3,
lambda_ell2 = 5/2,
lambda_ell1 != lambda_ell2.
```

Both finite order formulas are `1` in this example.

## Source reproduction

`threads/06-dln-translation/reproduction-definition3-l-eq-two-branch-formula-disagreement-a6.md`

## Verification

Focused elaboration and module build passed:

```text
cd lean
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
```

## Nonclaims

This is a finite Definition 3/Theorem 2 diagnostic only.  It is not a
correction of Aoyagi's theorem, not an analytic RLCT ambiguity theorem, and not
a chart, Eq5, normal-crossing, pole-order, or RLCT extraction result.
