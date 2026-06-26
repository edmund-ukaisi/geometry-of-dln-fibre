# Statement Card - A2 Case 2 residual-factor product selected-center matrix

## Claim

If the displayed Case 2 post-pivot lower product is the selected-center
coordinate matrix after endpoint reindexing, then the unreindexed two-edge
`residualFactorProduct` is exactly that selected-center coordinate matrix.

## Lean Names

```text
Matrix.eq_of_submatrix_equiv_eq
residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_submatrix
```

## Boundaries

Finite matrix reindexing only.  The displayed RHS identity, residual factors,
endpoint equivalences, and source production remain hypotheses.  The
post-pivot domains are `(S,J+1)`.
