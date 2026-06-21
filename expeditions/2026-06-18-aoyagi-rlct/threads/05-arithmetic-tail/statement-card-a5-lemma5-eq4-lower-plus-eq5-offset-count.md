# Statement Card - A5 Lemma 5 Eq4 Lower Plus Eq5 Offset Count

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_le_min`

## Claim

In the rising region, a supplied Eq4 lower own-coordinate value adds one value
to the strict Eq5 offset-value set.

## Inputs

- Guards `1 <= ell`, `1 <= p`, `p <= a`, and `p <= ell-a`.
- Source-selected sum and strict selected-width hypotheses.
- Supplied Eq4 piecewise source-vector certificate.

## Proves

```text
(insert (T (C.point p - 1))
  (aoyagiLemma5Eq5OffsetValueSet ell a p M m)).card
  =
(aoyagiLemma5Eq5OffsetValueSet ell a p M m).card + 1.
```

## Does Not Prove

- Source-label legality for the Eq4 lower endpoint.
- Construction of Eq4 or Eq5 displayed vectors.
- Upper endpoint realisation by Eq3.
- All-coordinate coverage, all-branch packaging, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(4)` and `(5)`, PDF pp. 26-27, represented by
supplied piecewise data and finite count arithmetic.
