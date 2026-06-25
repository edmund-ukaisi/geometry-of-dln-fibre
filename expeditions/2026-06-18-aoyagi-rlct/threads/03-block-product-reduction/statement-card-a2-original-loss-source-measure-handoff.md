# Statement Card - A2 original loss source-measure handoff

## Statement

If the fixed-base source-rank stratum is measurable, then the self-base
original-loss lower bound holds a.e. after shrinking to an open source
neighborhood:

```text
exists c > 0, exists U open with x0 in U,
  ae x for mu.restrict (U inter sourceStratum),
    (c / 2) * (regularSquareSum(x) + residualSquareSum(x))
      <= lossDLN d [T(B)]_b (chainMapMatrixTuple b (Cedge x)).
```

There is also a first-projection product-measure version over

```text
(mu.restrict (U inter sourceStratum)).prod nu.
```

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase
```

## Dependencies

- `exists_pos_const_half_regular_add_residual_squareSum_eventually_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_source`;
- `exists_open_ae_restrict_inter_of_eventually_nhdsWithin`;
- `exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin`.

## Role In A2

This packages the original square-Frobenius self-base lower bound for use by
measure-theoretic consumers.  It is the original-loss analogue of the existing
adapted-square-sum local source-measure handoff.

## Nonclaims

No product-coordinate chart, no independent regular fiber variable, no
fiber-uniform lower bound, no signed-box pushforward proof, no
density/Jacobian transport, no normal-crossing theorem, no pole-order
computation, and no RLCT extraction is proved.
