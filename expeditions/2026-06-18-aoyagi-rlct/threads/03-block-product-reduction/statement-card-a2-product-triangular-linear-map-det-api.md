# Statement card - A2 product triangular linear-map determinant API

Status: Lean-proved; xhigh-reviewed.

## Claim

For finite free modules `M` and `N`, arbitrary block-triangular linear maps on
`M x N` have determinant equal to the product of their diagonal determinants:

```text
det ((x,y) |-> (f x + h y, g y)) = det f * det g
det ((x,y) |-> (f x, h x + g y)) = det f * det g.
```

## Lean status

Proved in `lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`.

Definitions and theorems:

```text
linearMapUpperTriangular
linearMapUpperTriangular_det_eq_mul
linearMapLowerTriangular
linearMapLowerTriangular_det_eq_mul
```

## Caveat

This is only determinant infrastructure.  It has not yet been instantiated to
the retained-passive true `fderiv` or to a full retained-passive shear
factorization.
