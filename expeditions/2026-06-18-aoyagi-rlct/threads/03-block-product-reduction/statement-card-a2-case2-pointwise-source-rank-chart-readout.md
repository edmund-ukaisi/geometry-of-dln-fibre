# Statement card - A2 Case 2 pointwise source-rank chart readout

Status: Lean theorem added; focused build passed locally.

Reproduction:
`reproduction-a2-case2-pointwise-source-rank-chart-readout.md`.

Review:
`review-a2-case2-pointwise-source-rank-chart-readout.md`.

## Lean Declaration

File:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`.

Theorem:

```text
case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap
```

## Claim

For an arbitrary continuing Case 2 selected-entry chart coordinate `yNext`,
the endpoint-transported retained-passive p.13 source edge family:

- lies in `paperEndpointFixedBaseSourceRankStratum` under the supplied
  pointwise edge-rank equations;
- lies in `paperEndpointFixedBaseRetainedPassiveP13LocalSource`;
- has fixed-base residual-coordinate map equal to the selected-entry chart
  map at `yNext`, through `residualCoordEquiv`.

## Hypotheses

The rank hypotheses are pointwise:

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
r + rank(case2SuccessorSelectedEntryMatrix ... yNext ...) = rEdge 1.
```

No successor-rank arithmetic is proved.

## Proof Inputs

The theorem packages three existing pointwise sockets:

```text
case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

## Verification

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb \
  DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

passed on 2026-06-29.

## Nonclaims

No selected-entry source coverage, source/image equality, exact-rank
openness, source-prior transport, Jacobian compatibility, normal crossings,
pole order, or RLCT is proved.  The coordinate readout is through the
displayed `residualCoordEquiv`, not a raw same-domain equality.
