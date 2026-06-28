# A2 retained-passive Case 2 canonical chart selected-entry square-sum

Status: Lean proved; focused build, local gates, full build, and xhigh review
passed after a documentation status correction.

## Claim

In the two-edge retained-passive suffix case `M = 1`, suppose the two factors
of the canonical topology tuple are Aoyagi's displayed Case 2 post-pivot
residual block and following free factor after endpoint reindexing.  Suppose
also that the displayed two-edge product has the selected-entry
center-coordinate readout entrywise.  Then the canonical p.13 chart-side
residual square-sum is the selected-entry center residual.

This removes the previously supplied selected-entry residual-factor matrix
hypothesis in the exact two-edge Case 2 topology-tuple lane.

## Pen-and-paper reproduction

Let

```text
rho = Fin (finrank U0),
kappa = throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U0.
```

For a determinant-chart topology tuple `z`, the canonical residual readout
bridge identifies the p.13 chart-side residual coordinates with

```text
value (residualFactorProduct (ofTopologyTuple z).C (Fin.last 2) 0).
```

Because `M = 1`, this is the whole two-edge suffix product.  Write

```text
D = (ofTopologyTuple z).C 1,
F = (ofTopologyTuple z).C 0.
```

The Case 2 hypotheses identify, after endpoint equivalences,

```text
D.submatrix e2 e1 = case2DisplayedPostPivotResidualBlock,
F.submatrix e1 e0 = case2DisplayedPostPivotFreeFollowingFactor.
```

The displayed product hypothesis says that every entry of the displayed
product is

```text
CenterCoord.chartMap pivot y (residualCoordEquiv (e2 i, e0 t)).
```

The two-edge `ofTopologyTuple` adapter therefore gives the concrete matrix
identity

```text
residualFactorProduct (ofTopologyTuple z).C (Fin.last 2) 0
  = matrix (fun c => CenterCoord.chartMap pivot y (residualCoordEquiv c)).
```

Applying the already proved canonical chart selected-entry square-sum bridge
to this matrix identity gives

```text
aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 id
    (sourceChart (topologyTupleEdgeRawOrder z)))
  = CenterCoord.residual pivot y.
```

The final equality is the finite reindexing of the residual coordinate
square-sum by `residualCoordEquiv` and the definition of the selected-entry
center residual.

## Scope boundary

The theorem is two-edge only.  It does not identify a longer canonical suffix
with a selected-entry matrix.  For a longer suffix, the Case 2 window remains
inside outside factors.  It also does not prove residual zero-locus nullity,
chart-side a.e. positivity, finite negative-power integrability, density
transport, normal crossings, pole order, or RLCT extraction.
