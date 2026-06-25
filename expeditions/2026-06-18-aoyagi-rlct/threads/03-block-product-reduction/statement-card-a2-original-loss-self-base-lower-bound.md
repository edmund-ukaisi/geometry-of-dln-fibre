# Statement Card - A2 original loss self-base lower bound

## Statement

At a continuous self-base paper chain, there is a positive constant `c > 0`
such that eventually on the fixed-base source-rank stratum,

```text
(c / 2) *
  (regularSquareSum(x) + residualSquareSum(x))
  <=
lossDLN d [T(B)]_b (chainMapMatrixTuple b (Cedge x)).
```

Here `[T(B)]_b` is the matrix of the base reversed endpoint chain map in the
same original endpoint bases `b` used to build `chainMapMatrixTuple`.

## Lean Name

```text
exists_pos_const_half_regular_add_residual_squareSum_eventually_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_source
```

## Dependencies

- `exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_selfBase_nhdsWithin_source`;
- `exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple`.

## Role In A2

This is the source-filter original-loss lower-bound bridge for the actual
chain-edge family near the base point.  It moves the endpoint comparison into
the p.13 self-base product-reduction lower-bound pipeline.

## Nonclaims

No product-coordinate chart, no independent regular fiber variable, no
signed-box source-measure transport, no density/Jacobian transport, no
statistical/KL/covariance loss, no arbitrary tuple theorem, no normal
crossings, no pole order, and no RLCT extraction is proved.
