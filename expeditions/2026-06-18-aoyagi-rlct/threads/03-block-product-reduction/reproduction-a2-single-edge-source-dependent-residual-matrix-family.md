# Reproduction - A2 single-edge source-dependent residual-matrix family

Date: 2026-06-25.

Status: pen-and-paper reproduction before Lean.  This is one-edge finite
p.13 product-coordinate algebra.

## Source Boundary

Aoyagi p.13 treats the regular coordinates `Ctop - I`, `F2`, `F3` and a
residual block `D`.  In the one-edge endpoint-collapse case, the residual
block can be prescribed directly.  This is different from the multi-edge case,
where the terminal residual product must factor through all intermediate
residual indices.

This note packages the one-edge construction when the residual matrix is a
base-point-dependent family

```text
Dbase x : Matrix μ ν ℝ.
```

It is independent of the quiver/LR paper and does not construct source
coverage or measure transport.

## Calculation

Fix a base point `x` and a Euclidean regular-coordinate vector `u`.  Decode
`u` into

```text
F2(u), F3(u), Ctop(u) = I + X(u).
```

Define the unique fixed-base edge matrix by

```text
G(x,u) =
[ Ctop(u),          -Ctop(u) F2(u)
  -F3(u) Ctop(u),   Dbase(x) + F3(u) Ctop(u) F2(u) ].
```

Realise this matrix as a continuous fixed-base reverse-edge family using the
existing prescribed-matrix realisation.  At the single point `(x,u)`, the
fixed-base product-difference coordinate theorem for one edge gives

```text
ProductDifferenceCoordinateMap(G(x,u))
  = value(Ctop(u)-I, F2(u), F3(u), Dbase(x)).
```

Because `Ctop(u)-I`, `F2(u)`, and `F3(u)` were decoded from `u`,

```text
regular coordinates = u,
residual coordinates = value(Dbase(x)).
```

The determinant-chart condition is exactly

```text
IsUnit det(Ctop(u)).
```

Equivalently, by the raw residual-product theorem from the previous slice,
the transformed one-edge residual product of `G(x,u)` is also `Dbase(x)`.

## Lean Target

Add in `RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeProductCoordinateEuclidean_residualMatrix
continuousAt_paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
```

Add in `ChartTopology.lean`:

```text
continuous_productCoordinateSingleEdgeMatrix
```

The coordinate-readout theorem is pointwise in `(x,u)`.  The continuity theorem
requires `Continuous Dbase`; it does not need recursive determinant-chart
hypotheses because the one-edge product-coordinate matrix uses the supplied
residual block directly.

## Boundary

- This is one-edge only.
- It proves direct realisation of an arbitrary residual matrix family in the
  one-edge endpoint-collapse case.
- It does not generalise to multi-edge arbitrary terminal matrices; the
  formalised intermediate-rank obstruction remains in force there.
- It does not construct `Dbase`, construct a source chart, prove source
  coverage, identify source measures, produce normal crossings, prove pole
  order, or extract RLCT.
