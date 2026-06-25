# Statement Card - A2 Case 2 residual-factor product reindex

## Claim

A supplied two-edge residual-factor product, after explicit endpoint
reindexing and supplied factor identities, is Aoyagi's displayed Case 2
post-pivot free-`C'` product:

```text
(residualFactorProduct C 2 0).submatrix e_row e_right
  = case2DisplayedPostPivotFreeTwoEdgeFactorProduct.
```

## Lean Name

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix
```

## Boundaries

Finite reindexing only.  The theorem assumes the endpoint equivalences and
the two factor identities.  It does not construct `Cfac`, a selected-entry
matrix identity, source/image equality, normal crossings, pole order, or RLCT.

