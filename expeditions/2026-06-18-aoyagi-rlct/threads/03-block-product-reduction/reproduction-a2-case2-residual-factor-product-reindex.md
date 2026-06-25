# Reproduction - A2 Case 2 residual-factor product reindex

Date: 2026-06-25.

Status: Lean target implemented as a finite bridge theorem.

## Source Boundary

Aoyagi p. 13 uses ordered products of residual factors in the reduced
coordinates.  In the displayed Case 2 calculation on pp. 19-22, the local
post-pivot lower product is

```text
D_{J+1} * C'_+.
```

In the current Lean API this product is represented by
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct`, with first factor
`case2DisplayedPostPivotResidualBlock` and second factor
`case2DisplayedPostPivotFreeFollowingFactor`.

This note records only the finite reindexing bridge from the generic
two-edge `residualFactorProduct` API to that displayed Case 2 product.  The
residual-factor family, endpoint equivalences, and factor identities are
supplied hypotheses.

## Calculation

Let

```text
C_1 : Matrix kappa_2 kappa_1
C_0 : Matrix kappa_1 kappa_0.
```

The generic two-edge unfold gives

```text
residualFactorProduct C 2 0 = C_1 * C_0.
```

Suppose explicit equivalences identify the concrete Case 2 row, middle, and
right endpoints with `kappa_2`, `kappa_1`, and `kappa_0`, and suppose the two
reindexed factor identities are

```text
C_1.submatrix e_row e_mid = D_{J+1},
C_0.submatrix e_mid e_right = C'_+.
```

Then Mathlib's `Matrix.submatrix_mul_equiv` gives

```text
(C_1 * C_0).submatrix e_row e_right
  = C_1.submatrix e_row e_mid * C_0.submatrix e_mid e_right
  = D_{J+1} * C'_+.
```

The final right side is definitionally
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct`.

## Lean Target

Implemented in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix
```

The module imports both `ProductReduction` and `BlowupArithmetic` so neither
lower-level file needs a new dependency on the other.

## Nonclaims

- No concrete displayed Case 2 dependent `Cfac` family is constructed.
- No fixed-base endpoint equivalence is constructed.
- No selected-entry coordinate-matrix RHS identity is proved.
- No source/image equality or source-measure transport is proved.
- No normal crossings, pole order, or RLCT theorem is proved.

