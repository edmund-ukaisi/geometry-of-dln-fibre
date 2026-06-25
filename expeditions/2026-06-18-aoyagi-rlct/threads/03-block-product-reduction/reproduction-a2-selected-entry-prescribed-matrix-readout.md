# Reproduction - A2 selected-entry prescribed-matrix readout

Date: 2026-06-25.

Status: Lean formalised; review pending.

## Source Boundary

This is an API bridge under the same source boundary as
`reproduction-a2-selected-entry-source-chart-coverage-boundary.md`.
Aoyagi's pp. 15-21 selected-entry display does not construct a fixed-base
edge-family chart.  This checkpoint only says how a future fixed-base matrix
formula would feed the existing residual-readout endpoint.

## Pen-And-Paper Check

Suppose a future source-chart algebra calculation supplies a fixed-base
edge-matrix family

```text
Ebase(x)_p.
```

Lean already has the prescribed-matrix realisation

```text
CedgeBase(x) = continuousReverseEdgeFamilyOfMatrices(Ebase(x)).
```

By the fixed-base realisation theorem, reading the fixed-base edge matrices of
this realised edge family recovers the original prescribed matrices:

```text
edgeMatrix(CedgeBase(x))_p = Ebase(x)_p.
```

Therefore, if the supplied matrix-family calculation proves

```text
residualProduct(Ebase(chartMap(pivot,y)))
  = matrix(c ↦ chartMap(pivot,y)_(e c)),
```

then the previous residual-product matrix readout bridge applies to the
realised `CedgeBase` and gives

```text
residualCoordinateMap(CedgeBase, chartMap(pivot,y))_c
  = chartMap(pivot,y)_(e c).
```

## Lean Target

The new Lean bridge is:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_prescribedEdgeMatrix_residualProduct_eq_matrix
```

It is a wrapper around the matrix-level residual-product readout bridge plus
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices`.

## Boundary

- The theorem does not construct `Ebase`.
- The theorem does not prove the selected-entry residual-product matrix
  identity.
- The theorem does not construct the residual-index equivalence.
- The theorem does not prove source coverage, source-measure transport,
  normal crossings, pole order, or RLCT.
