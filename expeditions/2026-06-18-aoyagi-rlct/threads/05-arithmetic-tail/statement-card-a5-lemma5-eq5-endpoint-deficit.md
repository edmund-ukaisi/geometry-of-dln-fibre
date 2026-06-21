# Statement Card - A5 Lemma 5 Eq5 Endpoint Deficit

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcess_eq_self_iff_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalExcess_le_pred_of_not_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDeficit`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDefect`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_offsets_endpointDeficit_split`

## Claim

Eq5 strict offsets have a precise finite endpoint deficit.

For coordinate `p`, the same-coordinate interval has cardinality
`1 + excess_p`, while the Eq5 strict offset set has cardinality
`min(excess_p, p-1)`.  Therefore Eq5 always has an upper-endpoint deficit, and
it has one additional lower-endpoint deficit exactly in the rising region:

```text
1 <= p, p <= a, p <= ell-a.
```

The set-level split says that for every positive coordinate, either:

```text
Eq5Offsets = Interval.erase upperEndpoint
```

or we are in the rising region and:

```text
Eq5Offsets = (Interval.erase upperEndpoint).erase lowerEndpoint.
```

## Inputs

- `a <= ell`;
- for the cardinal formula, `p < ell+1`;
- for the set split, `1 <= p` and `p < ell+1`.

## Proves

The interval excess equals `p` iff `p<=a` and `p<=ell-a`, and outside that
region the excess is at most `p-1`.

The cardinal formula is:

```text
interval.card =
  Eq5Offsets.card + 1
    + if 1<=p and p<=a and p<=ell-a then 1 else 0.
```

The set split packages the existing rising and non-rising Eq5 finite-set
equalities into one endpoint-deficit disjunction.

## Does Not Prove

- Source construction of Eq5 branches.
- Source construction of the missing endpoint branches.
- Source-label legality, terminal `tilde t=0`, chart coverage, all-coordinate
  branch-family coverage, pole order, normal crossings, or RLCT extraction.

## Source

This is finite arithmetic and set bookkeeping below Aoyagi Lemma 5's displayed
branch-family realisation boundary.  It does not add a citation boundary.
