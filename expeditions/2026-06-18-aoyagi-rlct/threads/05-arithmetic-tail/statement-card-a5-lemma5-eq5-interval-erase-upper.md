# Statement card - A5 Lemma 5 equation (5) interval erase-upper equality

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_upperEndpoint_not_mem_insert_lowerEndpoint_offsets_of_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min`

## Claim

In the rising region `1<=p`, `p<=a`, `p<=ell-a`, the finite set consisting of
the lower endpoint and the strict Eq5 offset values is exactly the
same-coordinate interval value set with the upper endpoint erased:

```text
insert Htilde_p Eq5OffsetValueSet_p
  = erase Htilde'_p (HtildeIntervalValueSet_p).
```

## Inputs

- `a <= ell`.
- `1 <= p`, `p <= a`, and `p <= ell-a`.
- Arbitrary `M` and selected-width family `m`.

## Proves

- The upper endpoint belongs to the same-coordinate interval.
- The upper endpoint is not in the lower-plus-strict-offset inserted set.
- The inserted set equals the interval value set with the upper endpoint
  erased.

## Does Not Prove

- Realisation of the upper endpoint by equation `(3)` or `(4)`.
- Construction of any displayed vector.
- Source-label legality, terminality, admissibility, chart coverage, Lemma 5
  order count, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 interval count and equation `(5)`, PDF pp. 25-27.
