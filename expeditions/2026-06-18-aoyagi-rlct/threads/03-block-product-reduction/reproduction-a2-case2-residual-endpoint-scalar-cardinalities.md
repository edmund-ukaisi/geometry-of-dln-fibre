# Reproduction - A2 Case 2 residual endpoint scalar cardinalities

## Source Shape

After the displayed Case 2 pivot at level `J + 1`, the successor residual block
uses the row and column index types

```text
Case2ResidualRowIndex n S (J + 1),
Case2ResidualColIndex n S (J + 1).
```

By definition these are the finite intervals

```text
rows: J+2, ..., prefixMinNat n S,
cols: J+2, ..., n (S + 1).
```

The fixed-base endpoint-cardinality theorem from the previous rung wants the
scalar equalities

```text
card (Case2ResidualColIndex n S (J + 1)) = H 2 - r,
card (Case2ResidualRowIndex n S (J + 1)) = H 1 - r.
```

These equalities are finite interval arithmetic once the current source rank
and displayed widths are identified as

```text
r = J + 1,
H 2 = n (S + 1),
H 1 = prefixMinNat n S.
```

## Derivation

The existing interval-cardinality lemmas give, for any `J`,

```text
card (case2ResidualBlockCols n S J) = n (S + 1) - J,
card (case2ResidualBlockRows n S J) = prefixMinNat n S - J.
```

Apply them at `J + 1`.

For columns:

```text
card (Case2ResidualColIndex n S (J + 1))
  = n (S + 1) - (J + 1)
  = H 2 - r.
```

The last equality rewrites `H 2` to `n (S + 1)` and `r` to `J + 1`.

For rows:

```text
card (Case2ResidualRowIndex n S (J + 1))
  = prefixMinNat n S - (J + 1)
  = H 1 - r.
```

The last equality rewrites `H 1` to `prefixMinNat n S` and `r` to `J + 1`.

These two equalities can then be fed into
`case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData`,
leaving only the free right endpoint `tau` scalar equality explicit.

## Boundary

This derivation proves the residual row and residual-column scalar
cardinalities only under explicit width/rank identifications.  It does not
prove those identifications from source data, does not construct `tau`, and
does not identify the `tau` cardinality `H 3 - r`.

## Proved / Assumed / Reused / Deferred

**Proved by this reproduction.** The residual-column and residual-row scalar
cardinality equalities for the successor Case 2 residual block, and the
corresponding source-data endpoint-cardinality theorem with only `hTau`
remaining as an endpoint scalar-size input.

**Assumed.** `r = J + 1`, `H 2 = n (S + 1)`, `H 1 = prefixMinNat n S`,
fixed-base source data, and `hTau : card tau = H 3 - r` for the source/free
endpoint.

**Reused.** `case2ResidualBlockCols_card`,
`case2ResidualBlockRows_card`, and
`case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData`.

**Deferred.** Construction of `tau`; proof of `hTau`; proof that source data
forces these width/rank identifications in the intended chart; canonical
endpoint labels; selected-entry preservation; source-prior transport; Jacobian
comparison; normal crossings; pole order; RLCT.
