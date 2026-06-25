# Statement Card - A2 finite basis-change square-sum comparison

## Statement

If a finite real matrix `T` is obtained from another finite real matrix `M` by
fixed left and right multiplication,

```text
T = L * M * R,
```

then there exists `c > 0` such that

```text
c * squareSum(T) <= squareSum(M).
```

Consequently, for two fixed finite bases `bE,bF` and `bE',bF'` of the source
and target of a real linear map `f`, there is a positive constant, depending
only on those fixed bases, such that

```text
c * squareSum([f]_{bE,bF}) <= squareSum([f]_{bE',bF'}).
```

## Lean Names

```text
exists_pos_const_matrixCoordinateSquareSum_le_of_mul_eq
exists_pos_const_forall_matrixCoordinateSquareSum_le_mul
exists_pos_const_linearMap_toMatrix_squareSum_le_of_basis_change
exists_pos_const_forall_linearMap_toMatrix_squareSum_le_of_basis_change
```

## Dependencies

- `matrixCoordinateSquareSum_mul_mul_le_mul`;
- `const_mul_matrixCoordinateSquareSum_le_of_mul_eq_of_multiplierSquareSum_mul_le`;
- `LinearMap.toMatrix_comp`;
- finite real coordinate square-sum nonnegativity.

## Role In A2

This is the finite basis-change ingredient for any future comparison between
fixed adapted endpoint Frobenius coordinates and original endpoint coordinates.
It is global in the endpoint map and does not require local source data.

## Nonclaims

No `lossDLN` comparison, no tuple-to-chain-map product bridge, no p. 13 product
chart, no source-rank openness, no density/Jacobian transport, no
statistical/KL/covariance loss comparison, no normal crossings, no pole order,
and no RLCT extraction is proved.
