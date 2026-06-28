# A2 retained-passive canonical chart selected-entry square-sum bridge

Status: Lean proved; focused build, local gates, and xhigh review passed.

## Claim

On the retained-passive determinant chart, suppose the canonical residual
factor product has already been identified with one selected-entry chart
matrix:

```text
residualFactorProduct (ofTopologyTuple z).C last 0
  = matrix (fun c => CenterCoord.chartMap pivot y (e c)).
```

Then the canonical chart-side residual square-sum is the selected-entry
center residual:

```text
aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 id
    (sourceChart (topologyTupleEdgeRawOrder z)))
  = CenterCoord.residual pivot y.
```

Here `e` is the finite equivalence from Aoyagi residual-block coordinate
indices to the selected-entry center.

## Pen-and-paper reproduction

Let

```text
R(z) = residualFactorProduct (ofTopologyTuple z).C last 0.
```

The already proved canonical chart readout gives, for every residual coordinate
index `c`,

```text
residualCoordinate(z, c) = value(R(z), c).
```

Assume the selected-entry matrix identity

```text
R(z) = matrix (fun c => chi_p(y)_(e c)),
```

where `chi_p = CenterCoord.chartMap pivot`.  Since `value (matrix f) = f`,
the coordinate readout is pointwise

```text
residualCoordinate(z, c) = chi_p(y)_(e c).
```

Therefore the residual square-sum is

```text
sum_c residualCoordinate(z,c)^2
  = sum_c chi_p(y)_(e c)^2.
```

The equivalence `e` reindexes the finite sum over residual coordinates by the
finite center, so

```text
sum_c chi_p(y)_(e c)^2 = sum_q chi_p(y)_q^2.
```

By definition of `CenterCoord.residual`, the final square-sum is exactly

```text
CenterCoord.residual pivot y.
```

## Scope boundary

This bridge proves only the square-sum readout once the matrix identity is
supplied.  It does not prove the matrix identity for the full canonical suffix
product, zero-locus nullity, chart-side a.e. positivity, negative-power
integrability, selected-entry signed-box density transport, normal crossings,
pole order, or RLCT extraction.
