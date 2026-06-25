# Statement Card - A2 regular-suspension local measure handoff

## Statement

For fixed-base p.13 regular-coordinate source data, assume the source rank
stratum

```text
paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
```

is measurable.

Then the p.13 source-filter lower bound

```text
(1/2) * (regularSquareSum(x) + residualSquareSum(x))
  <= literalProductDifferenceSquareSum(x)
```

holds almost everywhere after restricting any base measure to a sufficiently
small open neighborhood intersected with the source rank stratum.

There is also a first-projection product version over

```text
(mu.restrict (U inter sourceStratum)).prod nu.
```

If `0 <= c` and a supplied base loss satisfies, locally on the source-rank
filter,

```text
c * literalProductDifferenceSquareSum(x) <= loss(x),
```

then the same handoff gives the restricted-measure a.e. inequality

```text
(c/2) * (regularSquareSum(x) + residualSquareSum(x)) <= loss(x),
```

again with a first-projection product version.

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_literal_regular_add_residual_squareSum_half_le
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_fst_literal_regular_add_residual_squareSum_half_le
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_fst_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
```

## Dependencies

- `LocalMeasureHandoff.lean`;
- p.13 fixed-base square-sum source comparisons in
  `RegularSuspensionCoordinates.lean`;
- supplied measurability of the fixed-base source rank stratum.

## Nonclaims

No measurable-source-stratum proof, p.13 product chart, source/product
coordinate identification, product-fiber regular-square lower bound, original
DLN loss comparison, density/Jacobian transport, residual-base integrability,
normal crossing, pole order, or RLCT extraction is proved.
