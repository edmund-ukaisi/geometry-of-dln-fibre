# Statement card - A2 Case 2 endpoint cardinalities from source data

## Claim

For the two-edge Case 2 post-pivot family, fixed-base source data and explicit
scalar size equalities for `tau`, the residual-column type, and the
residual-row type imply the pointwise endpoint-cardinality hypothesis used by
`case2EndpointTransportEquivs_of_card_eq`.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean
```

Target name:

```lean
case2PostPivotTwoEdgeDomain_card_eq_endpointComplementIndex_of_sourceData
```

## Proof Basis

The proof is by cases on `q : Fin 3`.  The three endpoint cases reduce by
definition to `tau`, `Case2ResidualColIndex n S (J+1)`, and
`Case2ResidualRowIndex n S (J+1)`.  The fixed-base endpoint side is computed
by

```lean
PaperEndpointFixedBaseRegularCoordinateSourceData.endpointComplementIndex_card_eq_H_rev_sub_rank
```

and the reverse-index values for `Fin 3` give the `H 3 - r`, `H 2 - r`, and
`H 1 - r` targets.

## Nonclaims

This is finite endpoint-cardinality bookkeeping.  It does not prove the three
scalar size equalities, construct `tau`, construct canonical endpoint labels,
preserve selected entries, compare source priors, measures, or Jacobians,
produce normal crossings, compute pole order, or extract RLCT.
