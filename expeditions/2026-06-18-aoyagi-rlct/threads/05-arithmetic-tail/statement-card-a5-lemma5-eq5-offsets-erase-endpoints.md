# Statement Card - A5 Lemma 5 Eq5 Offsets Erase Endpoints

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min`

## Claim

In the rising region, the strict equation `(5)` offset value set is the
same-coordinate interval value set with both endpoints erased:

```text
Eq5OffsetValueSet_p
  = (HtildeIntervalValueSet_p.erase Htilde'_p).erase Htilde_p.
```

## Inputs

- `a <= ell`.
- Rising-region hypotheses `1 <= p`, `p <= a`, and `p <= ell-a`.

## Proves

Only a finite-set equality obtained from the existing Eq5 lower-plus-offset
erase-upper equality and the existing proof that the lower endpoint is not a
strict Eq5 offset.

## Does Not Prove

- Eq3 or Eq4 realisation of the erased upper endpoint.
- Construction of Eq3, Eq4, or Eq5 displayed vectors.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF pp. 26-27.
