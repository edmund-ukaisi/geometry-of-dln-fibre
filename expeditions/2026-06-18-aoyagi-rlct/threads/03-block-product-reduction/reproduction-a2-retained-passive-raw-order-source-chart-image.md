# A2 retained-passive raw-order source-chart image

## Claim

The canonical raw-order retained-passive source chart has image exactly the
fixed-base retained-passive source edge-family set.

## Reproduction

Fix endpoint bases `W`, base edge maps `B`, the endpoint complement `U0`, and
write

```text
rho = Fin (finrank K U0)
kappa' = throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U0.
```

Let

```text
T = topologyTupleRawOrderSourceRecursiveDetChartSet
S = paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U0 hU0.
```

The canonical raw-order source chart is

```text
Phi(y) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
    (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)).
```

First take `y in T`.  The raw-order inverse theorem gives

```text
topologyTupleEdgeRawOrder (topologyTupleEdgeRawOrderInverse y) = y,
```

and the inverse datum lies in the determinant chart.  The fixed-base retained
passive readout theorem gives

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges (Phi y)
  = (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)).edgeMatrix.
```

After rewriting the right hand side through the raw-order tuple identity, this
is exactly

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges (Phi y)
  = edgeFamilyOfRawOrderTuple y.
```

Since `y in T` says that `edgeFamilyOfRawOrderTuple y` is in the
source-recursive determinant chart, this proves `Phi(y) in S`.

Conversely take `E in S`.  Put

```text
EMat = paperEndpointFixedBaseEdgeMatrixOfReverseEdges E,
data = sourceReadback EMat,
y = topologyTupleEdgeRawOrder (topologyTuple data).
```

The definition of `S` gives `EMat` in the source-recursive determinant chart.
Then `data.detChart`, so `topologyTuple data` lies in the determinant chart and
the raw-order tuple `y` lies in the raw-order source chart `T`.  Also

```text
topologyTupleEdgeRawOrderInverse y = topologyTuple data.
```

The source-readback edge-matrix theorem gives `data.edgeMatrix = EMat`, and the
fixed-base continuous-family reconstruction theorem gives

```text
Phi(y) = E.
```

Thus `Phi '' T = S`.

## Boundary

This is an image theorem for the already reduced retained-passive fixed-base
chart.  It is not original source-rank coverage for the DLN parameter space, it
does not transport an original prior, and it proves no residual positivity,
integrability, normal crossings, pole order, or RLCT extraction.
