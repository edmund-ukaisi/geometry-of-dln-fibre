# Statement card - A5 Lemma 5 equation (5) offset/excess decomposition

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcess_eq_eq5OffsetCard_add_risingIndicator`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min`

## Claim

For each coordinate `p`, the Lemma 5 interval excess decomposes into the
finite Eq5 strict-offset count plus one extra rising-coordinate contribution.

Writing

```text
e_p = aoyagiLemma5IntervalExcess ell a p,
```

Lean proves, under `a <= ell`,

```text
e_p =
  card(aoyagiLemma5Eq5OffsetValueSet ell a p M m)
    + if 1<=p and p<=a and p<=ell-a then 1 else 0.
```

The Eq5 offset set has cardinality `min(e_p,p-1)`, so the indicator accounts
exactly for the case `e_p=p`, where strict offsets `alpha<p` miss one value.
Lean also proves that, under `p<=a` and `p<=ell-a`, the lower endpoint
`Htilde_p` is not a member of the Eq5 strict-offset set.

## Inputs

- Natural numbers `ell`, `a`, `p`.
- The source range hypothesis `a <= ell`.
- Arbitrary `M` and selected-width family `m`; the count is independent of
  their values because the offset map is injective.

## Proves

- Pointwise finite decomposition of the interval excess.
- Compatibility between the closed excess formula and the Eq5 offset-value
  set cardinality.
- Exclusion of the lower endpoint from the strict Eq5 offset-value set in the
  rising part of the interval.

## Does Not Prove

- Realisation of the remaining indicator by equation `(3)` or `(4)`.
- Construction of any displayed vector.
- Source-label legality, terminal `tilde t=0`, vector admissibility, chart
  sequence, Lemma 5 order count, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 interval count and equation `(5)`, PDF pp. 25-27.
