# Statement Card - A5 Lemma 5 Eq4 Lower Endpoint and Eq5 Erase-Upper Set

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min`

## Claim

For a supplied equation `(4)` piecewise certificate in the rising region,
inserting the Eq4 own-coordinate value into the Eq5 strict-offset value set is
the same as inserting the abstract lower endpoint:

```text
insert (T(C.point p - 1)) Eq5OffsetValueSet_p
  = HtildeIntervalValueSet_p.erase Htilde'_p.
```

## Inputs

- Eq4 supplied piecewise certificate.
- Source-selected hypotheses used by the existing Eq4 own-coordinate theorem.
- Rising-region hypotheses `1<=p`, `p<=a`, and `p<=ell-a`.

## Proves

Only a finite-set equality obtained by rewriting Eq4's own-coordinate value to
`Htilde_p` and applying the existing Eq5 erase-upper equality.

## Does Not Prove

- Realisation of the erased upper endpoint.
- Construction of Eq4 or Eq5 displayed vectors.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(4)` and `(5)`, PDF pp. 26-27.
