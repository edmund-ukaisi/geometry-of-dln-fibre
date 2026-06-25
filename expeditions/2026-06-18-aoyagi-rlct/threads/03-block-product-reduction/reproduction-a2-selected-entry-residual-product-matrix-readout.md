# Reproduction - A2 selected-entry residual-product matrix readout

Date: 2026-06-25.

Status: Lean formalised; review pending.

## Source Boundary

This checkpoint follows the boundary in
`reproduction-a2-selected-entry-source-chart-coverage-boundary.md`.
Aoyagi's printed pp. 15-21 selected-entry calculation supports a displayed
finite matrix chart and Schur cleanup, but it does not construct the original
p.13 source chart or prove the fixed-base residual-product matrix identity
for a concrete `CedgeBase`.

## Pen-And-Paper Check

Let `E(y)` be the fixed-base edge-matrix family obtained from a base edge
family `CedgeBase` at the selected-entry chart point `chartMap(pivot,y)`.
The fixed-base residual coordinate map is defined by taking the deterministic
suffix state from `E(y)` and reading its `D` block:

```text
residualCoordinateMap(chartMap(y))
  = value(residualProduct(E(y))).
```

Suppose a later source-chart/algebra calculation supplies the matrix identity

```text
residualProduct(E(y))
  = matrix(c ↦ chartMap(pivot,y)_(e c)),
```

where `e : residualIndex ≃ center`.  Then for every residual coordinate `c`,

```text
residualCoordinateMap(chartMap(y))_c
  = value(residualProduct(E(y)))_c
  = value(matrix(c ↦ chartMap(pivot,y)_(e c)))_c
  = chartMap(pivot,y)_(e c).
```

The last equality is exactly the residual-index reconstruction lemma
`AoyagiResidualBlockCoordinateIndex.value_matrix`.

## Lean Target

The new Lean bridge is:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualProduct_eq_matrix
```

It converts the supplied matrix identity for
`ChartLocalSuffixState.residualProduct` into the pointwise readout required by
the selected-entry original-loss endpoint.

## Boundary

- The theorem does not construct `CedgeBase`.
- The theorem does not prove the residual-product matrix identity.
- The theorem does not prove an equivalence between the residual index and
  `center`.
- The theorem does not prove source coverage, source-measure transport,
  normal crossings, pole order, or RLCT.
