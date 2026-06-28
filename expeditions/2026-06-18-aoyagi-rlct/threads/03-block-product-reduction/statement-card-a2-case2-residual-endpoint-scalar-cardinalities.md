# Statement card - A2 Case 2 residual endpoint scalar cardinalities

## Claim

The successor Case 2 residual-column and residual-row endpoint cardinalities
are `H 2 - r` and `H 1 - r` once the displayed source rank and widths are
identified by `r = J + 1`, `H 2 = n (S + 1)`, and
`H 1 = prefixMinNat n S`.

## Lean Targets

File:

```text
lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean
```

Target names:

```lean
case2ResidualEndpoint_card_eqs_of_width_rank
case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData_width_rank
```

## Proof Basis

The first theorem is finite interval cardinality:

```lean
case2ResidualBlockCols_card
case2ResidualBlockRows_card
```

applied at `J + 1` and rewritten by the supplied width/rank equalities.

The second theorem feeds those two scalar equalities into
`case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData`,
so the endpoint-family cardinality conclusion still leaves the `tau` equality
explicit.

## Nonclaims

This is finite scalar-cardinality bookkeeping.  It does not prove `r = J + 1`,
the displayed width equalities, the `tau` cardinality, the construction of
`tau`, canonical endpoint labels, selected-entry preservation, source-prior or
measure transport, Jacobian comparison, normal crossings, pole order, or RLCT.
