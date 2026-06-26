# Reproduction - A2 Case 2 displayed product entrywise selected-center RHS

Date: 2026-06-26.

Status: Lean target implemented as finite matrix extensionality.

## Source Boundary

Aoyagi's Case 2 calculation on pp. 19-22 supports the displayed post-pivot
lower product

```text
D_{J+1} * C'_+
```

on the continuing residual domains `(S,J+1)`.  The previous bridge named this
product in Lean as

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime.
```

This reproduction does not prove from the paper that each displayed product
entry is the selected-entry chart coordinate.  That entrywise readout remains
an explicit hypothesis, to be supplied by later source/chart work.  The point
of this slice is narrower: once the entrywise readout is available, the matrix
RHS consumed by the residual-factor bridge follows by extensionality.

## Calculation

Let

```text
P = case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
```

with row domain `Case2ResidualRowIndex n S (J+1)` and column domain `tau`.
Let the endpoint reindexing equivalences be

```text
e2 : Case2ResidualRowIndex n S (J+1) ~= kappa2
e0 : tau ~= kappa0
```

and let

```text
phi : AoyagiResidualBlockCoordinateIndex kappa2 kappa0 ~= center.
```

Define the selected-center coordinate matrix

```text
M i j = centerCoord (phi (i,j)).
```

Assume the pointwise displayed readout

```text
P i t = centerCoord (phi (e2 i, e0 t))
```

for every displayed row `i` and column `t`.  Then

```text
M.submatrix e2 e0 i t
  = M (e2 i) (e0 t)
  = centerCoord (phi (e2 i, e0 t))
  = P i t.
```

Thus `P = M.submatrix e2 e0` by matrix extensionality.

Composing this with the previously landed theorem

```text
residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_submatrix
```

gives a direct residual-factor product bridge whose displayed-RHS hypothesis is
only the entrywise readout.

## Lean Targets

Implemented in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_centerCoordinateSubmatrix_of_entrywise
residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
```

## Nonclaims

- The pointwise displayed selected-center readout is still supplied.
- No compatible residual-factor family is constructed.
- No endpoint equivalence is constructed.
- No source production of `Cprime` is proved.
- No source/image equality, source-measure transport, chart coverage,
  Jacobian theorem, normal crossings, pole order, or RLCT theorem is proved.
