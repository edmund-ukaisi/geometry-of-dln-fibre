# A2 Case 2 concrete inverse-density cardinality wrapper

## Source calculation

The concrete p.13 inverse-density finite-integral theorem is stated after
choosing endpoint equivalences

```text
eNext : tau ~= Case2ResidualColIndex n S (J + 1),
e q   : case2PostPivotTwoEdgeDomain n S J tau q
          ~= throughSubspaceEndpointComplementIndex ... q.
```

These equivalences are not analytic data.  They are finite reindexings of the
endpoint coordinates in Aoyagi's Case 2 p.13 chart.  If the caller supplies the
two cardinality equalities

```text
card tau = card (Case2ResidualColIndex n S (J + 1)),

card (case2PostPivotTwoEdgeDomain n S J tau q)
  = card (throughSubspaceEndpointComplementIndex ... q),
```

Lean constructs noncanonical equivalences by

```text
case2EndpointTransportEquivs_of_card_eq
```

using `Fintype.equivOfCardEq`.

The finite-integral calculation is unchanged after this substitution.  The
p.13 inverse density remains

```text
invJacDensity(x,u)
  =
productReductionStepRawOrderInverseJacobianDensity
  (paperEndpointFixedBaseP13RawOrderTuple
    W2 B2 U0 hU0 (fun E => E) (x,u)).
```

The base map in the p.13 raw-order tuple is still the identity edge-family map
`fun E => E`; it is not the selected-entry value-coordinate chart.

## Lean target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_card_eq
```

The rank-supported restrict-open sibling uses the same constructed endpoint
equivalences and adds only the already-standard rank identities

```text
finrank range(totalMap) = r,
r + card tau = rEdge 0,
forall yNext, r + rank(successorSelectedEntryMatrix yNext) = rEdge 1.
```

It then calls the fixed-equivalence restrict-open theorem, replacing

```text
mu.restrict (U cap sourceStratum)
```

by

```text
mu.restrict U.
```

Declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_restrict_open_of_sourceRankSupport_card_eq
```

## Boundary

This is only the endpoint-cardinality specialization of the concrete
inverse-density finite-integral handoff.  It does not prove the cardinality
equalities, preserve endpoint labels, identify the original source prior,
prove raw-Haar or product-coordinate source transport, construct normal
crossings, compute pole order, or extract RLCT.
