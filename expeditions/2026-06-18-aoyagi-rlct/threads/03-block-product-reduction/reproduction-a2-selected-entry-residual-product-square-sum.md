# Reproduction - A2 selected-entry residual-product square-sum

Date: 2026-06-25.

Status: controller pen-and-paper reproduction before Lean.  This is a finite
readout-composition theorem, not source-chart construction.

## Source/Boundary Anchor

The current selected-entry local-source endpoint still needs a scalar residual
square-sum identity along the finite selected-entry chart:

```text
aoyagiCoordinateSquareSum(residualCoordinateMap(Phi_p(y)))
  = CenterCoord.residual(p,y).
```

Existing Lean already proves two pieces:

1. If the fixed-base suffix residual product equals the selected-entry chart
   matrix, then the fixed-base residual coordinate map reads each selected-entry
   chart coordinate, up to a finite equivalence.
2. If a coordinate family reads the selected-entry chart coordinates up to a
   finite equivalence, then its square-sum is the selected-entry residual.

This note composes those two pieces.

## Pen-And-Paper Check

Let `eta` be the fixed-base residual coordinate index and let

```text
e : eta ~= center
```

be a finite reindexing.  Suppose the suffix residual product has matrix
entries

```text
residualProduct(Phi_p(y))_{a,b}
  = matrix(c |-> Phi_p(y)_{e(c)}).
```

The residual-coordinate readout theorem says that the coordinate map `F`
therefore satisfies

```text
F(Phi_p(y))_c = Phi_p(y)_{e(c)}.
```

Then

```text
sum_c F(Phi_p(y))_c^2
  = sum_c Phi_p(y)_{e(c)}^2
  = sum_i Phi_p(y)_i^2
  = CenterCoord.residual(p,y),
```

where the middle equality is finite reindexing and the last equality is the
selected-entry residual square-sum identity already proved for `CenterCoord`.

## Lean Target

Add in `SelectedEntryOriginalLossLocalMeasure.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_residualProduct_eq_matrix
```

The theorem should return exactly the current scalar `hresidual_eq` shape from
the sharper supplied residual-product matrix identity.

## Boundary

- No construction of the fixed-base source-chart family `CedgeBase`.
- No proof of the residual-product matrix identity.
- No construction of the residual-index equivalence.
- No source image/coverage or source-stratum equality.
- No source-measure identification.
- No normal crossings, pole order, or RLCT.
