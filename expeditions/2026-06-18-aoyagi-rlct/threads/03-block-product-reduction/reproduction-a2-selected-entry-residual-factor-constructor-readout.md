# Reproduction - A2 selected-entry residual-factor constructor readout

Date: 2026-06-25.

Status: Lean target implemented for the finite readout composition; source
image equality remains supplied.

## Source Boundary

Aoyagi's p.13 reduction isolates the singular part of the local product as an
ordered product of residual factors `C^(s)`.  The selected-entry blow-up
calculation on pp. 19-22 gives elementary local chart algebra for updating one
residual block and its following factors.  After the p.20 convention
`b'_i = u b_i`, the selected scalar is already absorbed into the transported
weights; it is not an additional final factor.

The source supports a conditional compatible-factor calculation.  It does not
construct the factor family from the original p.13 source, prove local
source/image equality, or prove analytic coverage.

## Calculation

Let `Cfac x p` be a supplied residual-factor family indexed by a source
coordinate point `x`.  Let `uBase x` be the supplied regular-coordinate vector.
Define the fixed-base p.13 product-coordinate matrix family

```text
Ebase(x) =
  paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean
    (uBase x) (Cfac x).
```

The residual-factor constructor theorem gives, for every `x`,

```text
residualProduct(Ebase(x), last, 0)
  = residualFactorProduct(Cfac(x), last, 0).
```

The local selected-entry readout is evaluated at a selected-entry chart point
`chartMap(pivot,y)`.  Therefore the factor-product hypothesis must be indexed
as

```text
residualFactorProduct(Cfac(chartMap(pivot,y)), last, 0)
  = matrix(c ↦ chartMap(pivot,y)(e c)),
```

where `e` is the supplied residual-index equivalence.  Combining the two
equalities gives the prescribed fixed-base matrix residual-product identity at
`chartMap(pivot,y)`.  The existing prescribed-matrix readout bridge then
returns

```text
residualBlockCoordinateMap(Ebase, chartMap(pivot,y), c)
  = chartMap(pivot,y)(e c).
```

This is exactly the pointwise readout socket needed by the selected-entry
original-loss local theorem when the continuous edge family is the one
realized from the residual-factor product-coordinate matrices.

## Lean Target

Implemented in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualFactorProduct_eq_matrix
```

The proof defines `Ebase x` by the fixed-base residual-factor constructor,
uses the prescribed-matrix readout bridge, and discharges its residual-product
hypothesis with

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean_residualProduct_eq_residualFactorProduct
```

followed by the supplied factor-product selected-entry identity.

## Nonclaims

- No construction of `Cfac` from selected-entry or source-chart data.
- No proof that `residualFactorProduct (Cfac x) last 0` is the selected-entry
  coordinate matrix.
- No construction of the residual-index equivalence.
- No local source/image equality or chart coverage.
- No source-measure transport, density/Jacobian theorem, normal crossings,
  pole order, or RLCT.

## Review

Review:
`review-a2-selected-entry-residual-factor-constructor-readout.md`.

The xhigh source scout `Peirce` confirmed that Aoyagi supports conditional
compatible-factor algebra but not source/image equality.  The xhigh Lean/API
scout `Galileo` confirmed that this is the right non-thin composition: thread
the supplied `Cfac` through the actual residual-factor constructor and keep
`Cfac (chartMap pivot y)` in the product hypothesis.
