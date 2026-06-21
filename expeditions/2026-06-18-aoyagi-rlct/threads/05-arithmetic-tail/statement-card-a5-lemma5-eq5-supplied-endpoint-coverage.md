# Statement Card - A5 Lemma 5 Eq5 Supplied Endpoint Coverage

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedUpperLower_Eq5_offsets_eq_intervalValueSetNat_of_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedEndpointCoverage_Eq5_offsets_split`

## Claim

The Eq5 endpoint-deficit split can be converted into a supplied endpoint
coverage split.

Outside the rising region, a supplied upper endpoint value and the strict Eq5
offsets fill the same-coordinate interval.  In the rising region, a supplied
upper endpoint value, a supplied lower endpoint value, and the strict Eq5
offsets fill the same-coordinate interval.

## Inputs

- `a <= ell`;
- `1 <= p` and `p < ell+1`;
- a supplied upper endpoint equality

```text
Tupper(C.point p - 1) = Htilde'_p;
```

- in the rising case, a supplied lower endpoint equality

```text
Tlower(C.point p - 1) = Htilde_p.
```

## Proves

The rising-region theorem proves:

```text
insert Tupper (insert Tlower Eq5Offsets) = IntervalValueSet.
```

The split theorem proves the disjunction:

```text
insert Tupper Eq5Offsets = IntervalValueSet
```

or

```text
p<=a and p<=ell-a and
insert Tupper (insert Tlower Eq5Offsets) = IntervalValueSet.
```

## Does Not Prove

- That Eq3, Eq4, or Eq5 legally supplies the endpoint values.
- Source construction of displayed vectors.
- Terminal `tilde t=0`, chart coverage, all-coordinate branch-family coverage,
  pole order, normal crossings, or RLCT extraction.

## Source

This is finite supplied-data bookkeeping below Aoyagi Lemma 5's displayed
branch-family realisation boundary.  It does not add a citation boundary.
