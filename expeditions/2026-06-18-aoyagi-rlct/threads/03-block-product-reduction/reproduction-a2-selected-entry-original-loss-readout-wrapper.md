# Reproduction - A2 selected-entry original-loss readout wrapper

Date: 2026-06-25.

Status: Lean formalised; review pending.

## Source Boundary

This wrapper uses the boundary reproduced in
`reproduction-a2-selected-entry-source-chart-coverage-boundary.md`.
Aoyagi PDF pp. 15-21 support the displayed top-left selected-entry chart and
the finite `Q/P` Schur cleanup, but they do not provide source-stratum coverage
or an all-pivot analytic atlas.

## Calculation

The existing local original-loss endpoint consumes a scalar hypothesis

```text
sum_c D_c(chartMap(y))^2 = residual(pivot,y).
```

The previous square-sum checkpoint proved the finite algebra behind this:

```text
residual(pivot,y) = sum_i chartMap(pivot,y)_i^2.
```

Therefore it is enough to assume a coordinate readout

```text
e : residualIndex ≃ center
D_c(chartMap(y)) = chartMap(pivot,y)_(e c).
```

Then

```text
sum_c D_c(chartMap(y))^2
  = sum_c chartMap(pivot,y)_(e c)^2
  = sum_i chartMap(pivot,y)_i^2
  = residual(pivot,y).
```

The middle equality is finite reindexing by `e`.  No analytic source theorem is
used.

## Lean Target

The wrapper is:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_of_residualBlockCoordinateReadout
```

It calls the existing local source-stratum endpoint after deriving its
`hresidual_eq` hypothesis from
`SelectedEntrySignedBox.CenterCoord.aoyagiCoordinateSquareSum_eq_residual_of_coord_readout`.

## Boundary

- The local source/image equality remains a hypothesis.
- The fixed-base residual coordinate readout remains a hypothesis.
- The theorem does not prove source coverage, source-measure transport, an
  analytic Jacobian identity, normal crossings, pole order, or RLCT.
