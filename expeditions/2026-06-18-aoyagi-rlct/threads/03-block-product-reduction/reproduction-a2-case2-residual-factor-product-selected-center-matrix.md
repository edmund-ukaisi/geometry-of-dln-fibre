# Reproduction - A2 Case 2 residual-factor product selected-center matrix

Date: 2026-06-25.

Status: Lean target implemented as finite matrix reindexing.

## Source Boundary

Aoyagi's Case 2 calculation on pp. 19-22 supports the following finite
post-pivot matrix story:

- the selected residual entry is `d_{J+1,J+1}`;
- the selected chart writes this entry as `u` and the other residual-center
  entries as `u*d'`;
- the column operation gives `C' = Q^{-1} C`;
- the row operation gives the cleared block `D''' = blockdiag(1,D_{J+1})`;
- the continuing lower product is `D_{J+1} * C'_+`, then the proof advances
  from `J` to `J+1`.

The Lean object

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
```

is exactly this lower product after reindexing onto the next same-stage
residual row and column domains `(S,J+1)`.

## Calculation

The previous bridge proves that, for a supplied two-edge residual-factor
family `C` and supplied endpoint equivalences `e2`, `e1`, `e0`,

```text
(residualFactorProduct C (last 2) 0).submatrix e2 e0
  = case2DisplayedPostPivotFreeTwoEdgeFactorProduct ...
```

provided the two individual factors reindex to the post-pivot residual block
and following-factor tail.

Suppose additionally that the displayed lower product is the selected-center
coordinate matrix after the same endpoint reindexing:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct ...
  = matrix (fun c => centerCoord (residualCoordEquiv c)).submatrix e2 e0.
```

Then the two matrices before reindexing are equal, because submatrixing both
axes by equivalences is faithful.  Entrywise, for any row `i` and column `j`
of the unreindexed product, apply the submatrix equality at
`e2.symm i` and `e0.symm j`.

This upgrades the supplied displayed RHS identity from a reindexed lower-row
statement to the exact matrix identity expected by the selected-entry
readout socket.

## Lean Targets

Implemented in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`:

```text
Matrix.eq_of_submatrix_equiv_eq
residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_submatrix
```

## Orientation Guard

The post-pivot product uses `Case2ResidualRowIndex n S (J+1)` and
`Case2ResidualColIndex n S (J+1)`.  It must not be identified with the old
center `case2ResidualBlockPivotEntries n S J` without an explicit equivalence.

## Nonclaims

- The displayed selected-center RHS identity is still supplied.
- No compatible residual-factor family is constructed.
- No endpoint equivalence is constructed.
- No `Cprime` source production is proved.
- No chart coverage, source/image equality, transition regularity, Jacobian
  theorem, normal crossings, pole order, or RLCT theorem is proved.
