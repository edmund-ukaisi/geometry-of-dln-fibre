# A2 retained-passive raw-order source-chart homeomorphism

## Claim

The canonical raw-order retained-passive source chart is a homeomorphism from
the raw-order source-recursive determinant chart to the fixed-base retained
passive source edge-family set.

## Reproduction

Write

```text
rho = Fin (finrank K U0)
kappa' = throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U0.
```

There are three coordinate identifications already established.

First, determinant-chart retained-passive data and determinant-chart topology
tuples are the same product coordinates in two presentations:

```text
data |-> topologyTuple data,
z    |-> ofTopologyTuple z.
```

The identities `ofTopologyTuple (topologyTuple data) = data` and
`topologyTuple (ofTopologyTuple z) = z` give the inverse laws.  The topology on
retained-passive data is induced by `topologyTuple`, so both directions are
continuous on the determinant-chart subtypes.

Second, the raw-order map is a homeomorphism from the topology-tuple
determinant chart to the raw-order source-recursive determinant chart:

```text
z |-> topologyTupleEdgeRawOrder z,
y |-> topologyTupleEdgeRawOrderInverse y.
```

The inverse laws are exactly

```text
topologyTupleEdgeRawOrderInverse (topologyTupleEdgeRawOrder z) = z,
topologyTupleEdgeRawOrder (topologyTupleEdgeRawOrderInverse y) = y.
```

Third, fixed-base retained-passive determinant-chart data are homeomorphic to
the fixed-base continuous source edge-family set:

```text
data |-> paperEndpointFixedBaseRetainedPassiveP13SourceChart data,
E    |-> paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyReadback E.
```

Composing the inverse of the raw-order homeomorphism, the inverse of the
data/topology-tuple presentation change, and the fixed-base source edge-family
homeomorphism gives the desired homeomorphism:

```text
y |-> paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
        (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)).
```

This is definitionally the public canonical raw-order source chart
`paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart`.

The inverse sends a fixed-base source edge family `E` to

```text
topologyTupleEdgeRawOrder
  (topologyTuple
    (sourceReadback (paperEndpointFixedBaseEdgeMatrixOfReverseEdges E))).
```

The forward and inverse laws are therefore the three already-established
inverse laws composed in order.

## Boundary

This proves local inverse and continuity data for the reduced fixed-base
retained-passive source chart.  It is not original DLN source-rank coverage,
does not transport an original prior or measure, and proves no residual
positivity, integrability, normal crossings, pole order, or RLCT extraction.
