# Statement Card - A5 Lemma 5 Eq5 Non-Rising Coverage

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_upperEndpoint_not_mem_offsetValueSet`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_offsets_eq_interval_erase_upper_of_excess_le_pred`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedUpper_Eq5_offsets_eq_intervalValueSetNat_of_excess_le_pred`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedEq3Upper_Eq5_offsets_eq_intervalValueSetNat_of_plateau`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_plateau`

## Claim

For a fixed coordinate `p`, equation `(5)`'s strict offset values are:

```text
U_p - alpha,  1 <= alpha <= min(excess_p, p-1).
```

If `excess_p <= p-1`, then these values are exactly the same-coordinate
interval with the upper endpoint `U_p` removed.

Consequently, any supplied branch value equal to `U_p` fills the interval
together with Eq5 offsets.  In the plateau subcase `a<p<=ell-a`, a supplied
Eq3-shaped component provides such an upper endpoint value.

## Inputs

For the general finite-set equality:

- `a <= ell`;
- `p < ell+1`;
- `aoyagiLemma5IntervalExcess ell a p <= p-1`.

For the supplied-upper wrapper:

- a supplied value `Tupper (C.point p - 1) = Htilde'_p`.

For the Eq3-shaped plateau wrapper:

- `1 <= p`;
- `a < p`;
- `p <= ell-a`;
- a supplied `AoyagiLemma5Eq3PiecewiseSourceVector`.

## Proves

```text
Eq5OffsetValueSet = IntervalValueSet.erase upperEndpoint
```

under `excess<=p-1`, and:

```text
insert upperEndpoint Eq5OffsetValueSet = IntervalValueSet.
```

The Eq3 plateau wrapper instantiates the supplied upper endpoint using the
component value of the supplied Eq3-shaped certificate.

## Does Not Prove

- Construction of the Eq5 or Eq3 displayed source vectors.
- Source-label legality for the supplied upper endpoint.
- Terminal `tilde t=0`, chart coverage, branch-family coverage, pole order,
  normal crossings, or RLCT extraction.

## Source

This is finite interval bookkeeping below Aoyagi Lemma 5's displayed-family
realisation boundary.  It does not add a citation boundary.
