# Statement Card - A5 Lemma 5 Eq3-Shaped Component Interval Coverage

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_eq_intervalValueSetNat`

## Claim

For a rising-range coordinate `p`, a supplied Eq3-shaped component value and a
supplied Eq4 lower own-coordinate value fill the two endpoints missing from
the strict Eq5 offset set:

```text
insert (T3 (C.point p - 1))
  (insert (T4 (C.point p - 1))
    (aoyagiLemma5Eq5OffsetValueSet ell a p M m))
= aoyagiHtildeIntervalValueSetNat ell a M m p.
```

This is a component-value theorem.  It is not a claim that the Eq3-shaped value
is a legal source label or introduced label.

## Inputs

- Rising-region guards `1 <= p`, `p <= a`, and `p <= ell-a`.
- Source selected-width sum and strict source inequalities needed by the Eq4
  lower endpoint wrapper.
- Supplied Eq3-shaped piecewise source-vector certificate.
- Supplied Eq4 piecewise source-vector certificate.

## Proves

Only a finite-set equality for one same-coordinate interval, plus the
component equality
`T3(C.point p - 1) = aoyagiHtildeUpperNat ell a M m p`.

## Does Not Prove

- Source-label legality or introduced-label status for the Eq3-shaped
  component.
- Construction of Eq3, Eq4, or Eq5 displayed vectors.
- All-interval coverage, all-branch coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 Eq3-shaped upper branch and equations `(4)` and `(5)`, PDF
pp. 26-27, represented as supplied piecewise certificates plus the existing
Lean supplied-upper interval coverage theorem.
