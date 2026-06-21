# Statement Card - A5 Lemma 5 Supplied Upper and Eq4 Interval Coverage

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_le_min`

## Claim

For any rising-range coordinate `p`, a supplied upper endpoint value and a
supplied Eq4 lower own-coordinate value fill the two endpoints missing from
the strict Eq5 offset set:

```text
insert (Tupper (C.point p - 1))
  (insert (T4 (C.point p - 1))
    (aoyagiLemma5Eq5OffsetValueSet ell a p M m))
= aoyagiHtildeIntervalValueSetNat ell a M m p.
```

This is not a claim that printed Eq3 supplies the upper endpoint or a source
label; the upper equality is an explicit hypothesis.

## Inputs

- Rising-region guards `1 <= p`, `p <= a`, and `p <= ell-a`.
- Source selected-width sum and strict source inequalities needed by the Eq4
  lower endpoint wrapper.
- Supplied Eq4 piecewise source-vector certificate.
- Supplied upper endpoint equality
  `Tupper(C.point p - 1) = aoyagiHtildeUpperNat ell a M m p`.

## Proves

Only a finite-set equality for one same-coordinate interval.

## Does Not Prove

- Construction of an upper-endpoint displayed vector.
- That printed Eq3 supplies the upper endpoint.
- Source-label legality, introduced-label status, exponent certificates,
  terminality, admissibility, chart sequence, all-interval coverage, all-branch
  coverage, Lemma 5 order count, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 interval count and equations `(4)` and `(5)`, PDF pp. 26-27,
plus the existing Lean Eq4/Eq5 erase-upper equality.  The upper endpoint is
kept as supplied data in this theorem.
