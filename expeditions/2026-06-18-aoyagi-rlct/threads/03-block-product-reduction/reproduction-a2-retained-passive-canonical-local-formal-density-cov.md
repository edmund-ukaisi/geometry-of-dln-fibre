# A2 retained-passive canonical local formal/product-density COV

## Claim

The canonical fixed-base retained-passive local-source chart can consume the
formal and product raw-order Jacobian densities without an externally supplied
realization map.

## Reproduction

Let

```text
rho = Fin (finrank R U0)
kappa' = throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U0
T = topologyTupleRawOrderSourceRecursiveDetChartSet
S = topologyTupleDetChartSet
```

and define the canonical target-side source chart by

```text
sourceChart(y)
  = paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
      (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)).
```

For `y in T`, the inverse theorem gives

```text
topologyTupleEdgeRawOrder (topologyTupleEdgeRawOrderInverse y) = y.
```

The retained-passive source readback theorem identifies the fixed-base edge
matrix of `sourceChart(y)` with the edge matrix of
`ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)`.  The raw-order edge
family identity then gives

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges (sourceChart y)
  = edgeFamilyOfRawOrderTuple y.
```

Thus the canonical chart satisfies exactly the realization hypothesis of the
realized local-source theorem.

The a.e.-measurability hypothesis is also internal.  On the open chart `T`,
`topologyTupleEdgeRawOrderInverse` is continuous, `ofTopologyTuple` is
continuous, and the retained-passive p.13 source chart is continuous on the
determinant-chart subtype.  Hence `sourceChart` is continuous on `T`, and
therefore a.e.-measurable for `m.restrict T`.

Applying the realized local-source theorem with either

```text
J(z) = ofReal (retainedPassiveFormalRawOrderJacobianAbsDetAt z)
```

or

```text
J(z) = ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt z)
```

proves the canonical local-source formal/product-density COV.

## Boundary

This removes the external realization hypothesis only for the canonical
retained-passive chart-produced local source.  It still does not construct an
original source prior, identify signed-box densities, prove normal crossings,
compute pole order, or extract an RLCT.
