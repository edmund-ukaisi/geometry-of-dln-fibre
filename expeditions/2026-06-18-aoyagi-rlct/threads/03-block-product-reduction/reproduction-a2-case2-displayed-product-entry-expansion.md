# Reproduction - A2 Case 2 displayed product entry expansion

Date: 2026-06-26.

Status: Lean target implemented as finite matrix multiplication.

## Source Boundary

Aoyagi's Case 2 calculation on pp. 19-22 produces the post-pivot lower
product

```text
D_(J+1) * C'_+.
```

The row and intermediate column domains are the continuing residual domains
at `(S,J+1)`.  In Lean this product is named

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime.
```

This slice only expands that displayed product entrywise.  It does not
identify product entries with source-chart coordinates or selected-center
coordinates.

## Calculation

Let

```text
D = case2DisplayedPostPivotResidualBlock n hS hcont residual,
F = case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime.
```

Then by definition

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
  = D * F.
```

For a continuing row `i : Case2ResidualRowIndex n S (J+1)` and a target
column `t : tau`, the finite matrix-product formula gives

```text
(D * F) i t =
  sum_{j : Case2ResidualColIndex n S (J+1)} D i j * F j t.
```

This is exactly the entrywise displayed lower product supported by Aoyagi's
`D_(J+1) * C'_+`.

Unfolding the definition of the reindexed following-factor tail also gives
the same formula directly in terms of the free pivot-first matrix `Cprime`:

```text
P i t =
  sum_j D i j *
    Cprime (inr ((case2DisplayedPivotColComplementEquivResidualColSucc ...).symm j)) t.
```

## Lean Target

Implemented in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply_eq_sum_freeCprime
```

## Nonclaims

- No selected-entry center-coordinate readout is proved.
- No successor source-chart readout is proved.
- No endpoint equivalence is constructed.
- No compatible residual-factor family is constructed.
- No source production of `Cprime` is proved.
- No source/image equality, source-measure transport, chart coverage,
  Jacobian theorem, normal crossings, pole order, or RLCT theorem is proved.
