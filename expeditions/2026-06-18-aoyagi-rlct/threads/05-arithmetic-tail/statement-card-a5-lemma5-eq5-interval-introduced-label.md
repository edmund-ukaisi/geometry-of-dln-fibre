# Statement card - A5 Lemma 5 equation (5) interval and introduced-label wrappers

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_lowerEndpoint_mem_intervalValueSetNat_of_lt`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_card_of_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_subset_intervalValueSetNat_of_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_insertLower_offsetCard_add_one_eq_intervalCard_of_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_piecewise_ownBlock_intervalValue_introducedLabel_of_lastPoint_widthBound`

## Claim

In the rising region `1<=p`, `p<=a`, and `p<=ell-a`, the lower endpoint
`Htilde_p` can be inserted into the strict equation `(5)` offset-value set.
The resulting finite set:

- has cardinality `aoyagiLemma5IntervalExcess ell a p`;
- is contained in the same-coordinate interval value set;
- has cardinality one less than the full same-coordinate interval value set.

For a supplied equation `(5)` piecewise certificate, any own-block point
`C.block p S` also satisfies:

```text
T S in aoyagiHtildeIntervalValueSetNat ell a M m p,
T S = k-1,
introducedLabel L n S k S k.
```

The introduced-label state is the post-advance state `(S,k)`.

## Inputs

- `a <= ell`.
- Rising-region inequalities for the inserted-set count.
- Supplied equation `(5)` piecewise certificate for the source-label wrapper.
- Definition 3 selected-width sum and strict selected-width inequalities.
- Last selected cutpoint range `C.point ell <= L+1`.
- Explicit width lower bound `W_p <= n(S+1)`.

## Proves

- Finite set-level relation between the lower endpoint, strict Eq5 offsets,
  and the same-coordinate interval.
- Own-block interval membership, own-coordinate value `T S=k-1`, and
  post-advance introduced-label membership for supplied Eq5 data.

## Does Not Prove

- Construction of the supplied piecewise certificate.
- Realisation of the remaining interval value by equations `(3)` or `(4)`.
- Derivation of the width bound from Definition 3 alone.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 interval count and equation `(5)`, PDF pp. 25-27.
