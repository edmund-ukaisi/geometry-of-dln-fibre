# Review - A2 Case 2 topology-tuple source-family alignment

Reviewer: xhigh read-only checker `Helmholtz`.

Verdict: PASS.

The generic theorem is a valid corollary of
`paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData`
plus `ofTopologyTuple_topologyTuple`.  The determinant-chart membership for
`topologyTuple data` must use the `.2` direction of
`topologyTuple_mem_topologyTupleDetChartSet`, converting `data.detChart` to
membership in `topologyTupleDetChartSet`.

The Case 2 specialization should mirror the existing `W₂ : Fin 3`,
`B₂ : Fin 2`, `M := 1` fixed-base shape and discharge the determinant-chart
hypothesis with
`case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart`.

The nonclaim boundary is sufficient: the proposed theorem is only a
source-family presentation identity.  It is not endpoint provenance or
canonicity, source-rank coverage, source-image equality, pushforward-measure
transport, Jacobian comparison, normal crossings, pole order, or RLCT.
