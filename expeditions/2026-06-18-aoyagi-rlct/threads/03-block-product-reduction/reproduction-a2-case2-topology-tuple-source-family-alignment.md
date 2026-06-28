# Reproduction - A2 Case 2 topology-tuple source-family alignment

## Shape

Let `data` be retained-passive nonredundant coordinate data in the
determinant chart.  Let

```text
z := topologyTuple data.
```

The raw-order p.13 source chart is defined on a raw-order tuple `y` by first
reading `y` back with

```text
topologyTupleEdgeRawOrderInverse y
```

then applying `ofTopologyTuple`, and finally realizing the resulting retained
edge matrices as the fixed-base p.13 source edge family.

For a determinant-chart datum, the already-proved raw-order inverse identity is

```text
topologyTupleEdgeRawOrderInverse (topologyTupleEdgeRawOrder z) = z.
```

Thus, when `z = topologyTuple data`,

```text
ofTopologyTuple
  (topologyTupleEdgeRawOrderInverse
    (topologyTupleEdgeRawOrder (topologyTuple data)))
  = ofTopologyTuple (topologyTuple data)
  = data.
```

So the public raw-order source chart, evaluated at the raw-order tuple attached
to `data`, is the same source edge family as the direct fixed-base p.13 source
edge family attached to `data`.

For Case 2, take

```text
data :=
  (case2PostPivotSelectedEntryRetainedPassiveData
    (rho := Fin (finrank U0))
    n hS hcont hnext yNext eNext).endpointTransport e.
```

The determinant-chart hypothesis for this datum is already proved by

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart.
```

The same generic calculation therefore gives the concrete Case 2 source-family
alignment.

## Calculation

Start from the existing theorem

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
  (topologyTupleEdgeRawOrder z)
 =
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
  (ofTopologyTuple z)
```

under the hypothesis

```text
z in topologyTupleDetChartSet.
```

Set `z := topologyTuple data`.  The determinant-chart set condition is
equivalent to `data.detChart`, by `topologyTuple_mem_topologyTupleDetChartSet`.
The right-hand side then becomes

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
  (ofTopologyTuple (topologyTuple data)).
```

By `ofTopologyTuple_topologyTuple`,

```text
ofTopologyTuple (topologyTuple data) = data.
```

Therefore

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
  (topologyTupleEdgeRawOrder (topologyTuple data))
 =
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData data.
```

In the concrete Case 2 specialization, substitute the endpoint-transported
selected-entry datum and discharge `data.detChart` with the existing Case 2
determinant theorem.

## Boundary

This is a source-family presentation identity.  It identifies the concrete
datum recovered from the raw-order topology-tuple path with the original
endpoint-transported retained-passive datum.  It removes an `ofTopologyTuple`
/ direct-datum mismatch for the constructed chart path.

It does not construct endpoint equivalences, prove those equivalences canonical
or label preserving, prove source-rank coverage, compare priors or Jacobians,
prove normal crossings, compute pole order, or extract RLCT.

## Proved / Assumed / Deferred

**Proved by this reproduction.** The raw-order source chart evaluated on
`topologyTupleEdgeRawOrder (topologyTuple data)` agrees with the direct
fixed-base p.13 source edge family of `data`; in Case 2 this applies to the
endpoint-transported explicit selected-entry datum.

**Assumed.** For the generic theorem, `data.detChart`.  For the Case 2 theorem,
the endpoint equivalences `eNext` and `e`, the fixed-base context, and the
Case 2 continuation hypotheses `hS`, `hcont`, and `hnext`.

**Deferred.** Endpoint provenance, labelled selected-entry preservation,
source-prior transport, Jacobian comparison, source-rank coverage, normal
crossings, pole order, and RLCT.
