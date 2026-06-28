# Statement Card - A2 Case 2 topology-tuple source-family alignment

## Claim

For any retained-passive determinant-chart datum, the fixed-base p.13 raw-order
source chart evaluated at
`topologyTupleEdgeRawOrder (topologyTuple data)` is exactly the direct
fixed-base p.13 source edge family of `data`.

For the endpoint-transported explicit Case 2 selected-entry datum, the
determinant-chart hypothesis is discharged by the existing Case 2 determinant
theorem, giving the concrete alignment used by the Case 2 p.13 source path.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the p.13 retained-passive source-coordinate
construction, and pp. 19-22 for the Case 2 selected-entry datum.  Lean
dependencies:

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData
topologyTuple_mem_topologyTupleDetChartSet
ofTopologyTuple_topologyTuple
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
```

## Lean Target

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Expected declarations:

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_case2EndpointTransport_sourceEdgeFamilyOfData
```

## Nonclaims

No construction of endpoint equivalences, no proof of canonical or
label-preserving endpoint provenance, no selected-entry preservation theorem
for arbitrary noncanonical endpoint choices, no source-rank coverage, no
source-image equality, no pushforward-measure theorem, no source-prior
transport, no Jacobian comparison, no normal crossings, no pole order, and no
RLCT.

## Verification Plan

Run focused builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`, then
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker search,
direct axiom probes for the new declarations, and xhigh review.
