# Statement card - A2 Case 2 endpoint-transport pre-measure from cardinalities

## Claim

The Case 2 endpoint-transport fixed-base pre-measure input theorem can consume
explicit endpoint cardinality equalities instead of supplied endpoint
equivalence data.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Target name:

```lean
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_card_eq
```

## Proof Basis

Construct `equivs` using `case2EndpointTransportEquivs_of_card_eq`, set
`eNext := equivs.1` and `e := equivs.2`, and apply the existing supplied-
equivalence theorem.

## Nonclaims

This removes only the supplied endpoint-equivalence inputs from the first
pre-measure wrapper.  It does not prove the cardinality equalities, canonical
endpoint labels, selected-entry preservation, source-prior transport, Jacobian
comparison, positivity, integrability, normal crossings, pole order, or RLCT.
