# Reproduction - A2 single-edge selected-entry product-coordinate readout

Date: 2026-06-25.

Status: pen-and-paper reproduction before Lean.  This is a finite
selected-entry specialization of the one-edge p.13 product-coordinate algebra.

## Source Boundary

Aoyagi's p.13 product-coordinate expression separates regular variables from
the residual block.  In the one-edge endpoint-collapse case, the residual block
can be prescribed directly.  The previous one-edge slice formalized this with
an arbitrary base-dependent matrix family `Dbase x`.

Here we choose `Dbase` from the finite selected-entry chart coordinates.  Fix a
finite center, a pivot `pivot : center`, and an explicit residual-coordinate
equivalence

```text
residualCoordEquiv :
  AoyagiResidualBlockCoordinateIndex μ ν ≃ center.
```

The equivalence is part of the data.  There is no canonical equality between
the fixed-base residual-coordinate index and Aoyagi's selected-entry center
without this supplied alignment.

## Calculation

For a selected-entry coordinate point `y : center -> R`, set

```text
Dbase y =
  AoyagiResidualBlockCoordinateIndex.matrix
    (fun c =>
      SelectedEntrySignedBox.CenterCoord.chartMap pivot y
        (residualCoordEquiv c)).
```

At a regular coordinate vector `u`, the one-edge p.13 edge matrix is therefore

```text
[ Ctop(u),          -Ctop(u) F2(u)
  -F3(u) Ctop(u),   Dbase(y) + F3(u) Ctop(u) F2(u) ].
```

The generic one-edge source-dependent readout theorem gives, under
`IsUnit det(Ctop(u))`,

```text
regular coordinates = u,
residual coordinates = value(Dbase y).
```

By the residual-coordinate reconstruction identity `value_matrix`,

```text
value(Dbase y) c =
  SelectedEntrySignedBox.CenterCoord.chartMap pivot y (residualCoordEquiv c).
```

Hence the selected-entry specialization has exactly the expected finite
coordinate readout:

```text
regular coordinates = u,
residual coordinate c =
  selected-entry chart coordinate at residualCoordEquiv c.
```

## Continuity

The center-indexed selected-entry chart map is continuous: the pivot coordinate
is the identity, and every non-pivot coordinate is `y pivot * y i`.  Therefore
each scalar entry of `Dbase y` is continuous in `y`.  Matrix entrywise
continuity gives `Continuous Dbase`, and the generic one-edge residual-matrix
continuity theorem gives continuity of the realized edge family at every
`(y0,u0)`.

## Lean Target

Add in `SelectedEntryOriginalLossLocalMeasure.lean`:

```text
paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean
continuousAt_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
```

## Boundary

- One-edge only.
- Finite selected-entry coordinate readout only.
- The determinant-unit hypothesis on `Ctop(u)` remains explicit.
- The residual-coordinate equivalence is supplied data.
- The selected-entry chart is not inverted; when the pivot coordinate is zero,
  the chart collapses to the origin.
- No source coverage, source-stratum equality, source-measure transport,
  normal crossings, pole order, or RLCT is proved.
