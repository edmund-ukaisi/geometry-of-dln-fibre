# Statement Card - A2 original loss source-measure continuous-edge wrapper

## Statement

If the fixed-base edge family `Cedge` is globally continuous, then the
self-base original-loss source-measure handoff applies without a separate
source-stratum measurability hypothesis:

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
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_of_continuousEdge

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_of_continuousEdge
```

## Dependencies

- `measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous`;
- the original-loss source-measure handoff;
- global continuity implies `ContinuousAt Cedge x0`.

## Role In A2

This removes one routine measurable-set input from the concrete original
`lossDLN` self-base source-measure front end when the source edge family is
globally continuous.

## Nonclaims

No source-rank openness, no product-coordinate chart, no independent regular
fiber variable, no signed-box pushforward, no density/Jacobian transport, no
normal-crossing theorem, no pole-order computation, and no RLCT extraction is
proved.
