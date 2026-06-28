# Statement card - A2 Case 2 endpoint equivalences from cardinalities

## Claim

Explicit finite cardinality equalities are enough to construct the endpoint
equivalences required by the Case 2 endpoint-transport wrappers.  Separately,
fixed-base regular-coordinate source data computes every endpoint-compatible
complement cardinality as `H (q.rev.val + 1) - r`.

## Lean Targets

Files:

```text
lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

Target names:

```lean
case2EndpointTransportEquivs_of_card_eq
PaperEndpointFixedBaseRegularCoordinateSourceData.endpointComplementIndex_card_eq_H_rev_sub_rank
```

## Proof Basis

The endpoint-equivalence constructor is `Fintype.equivOfCardEq` applied once
to the successor right endpoint and pointwise to the three endpoint-family
cardinality equalities.

The source-data cardinality helper combines
`paperEndpointEndpointComplementIndex_card_eq_layerSubRank`,
`sourceData.dimensionConvention q.rev`, and the base product-rank equality in
`sourceData.localSourceCertificate.source_basepoint.1`.

## Nonclaims

These are finite cardinality and reindexing helpers only.  They do not produce
canonical endpoint labels, preserve selected entries, identify original source
priors, compare Jacobians, prove source-rank coverage, construct charts,
produce normal crossings, compute pole order, or extract RLCT.
