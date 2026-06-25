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

Finally, if the source filter already supplies uniform-in-fiber bounds

```text
forall u in ball(0,R),
  c * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),

forall u in ball(0,R), 0 <= density(x,u),

forall u in ball(0,R), density(x,u) <= C,
```

then there is a single open neighborhood `U` for which all three corresponding
product-measure a.e. bounds hold over

```text
(mu.restrict (U inter sourceStratum)).prod nu.
```

This supplies only the loss/density a.e. hypothesis shape for the finite-side
p.13 regular-coordinate adapter; residual positivity and residual
negative-power integrability remain separate inputs.

If those residual inputs are also supplied on the source rank stratum, namely
a.e. positivity of the residual square-sum and finite
`int^- ofReal(residualSquareSum^(-t))`, then the local bridge produces an
open neighborhood `U` on which the finite-side p.13 lower integral is finite
over

```text
(mu.restrict (U inter sourceStratum)).prod nu.
```

The exponent in the conclusion is

```text
t + aoyagiTheorem2RegularVariableCount N H r / 2.
```

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_literal_regular_add_residual_squareSum_half_le
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_fst_literal_regular_add_residual_squareSum_half_le
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_fst_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds
PaperEndpointFixedBaseRegularCoordinateSourceData.residualNegPowerIntegrableOn
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
```

## Dependencies

- `LocalMeasureHandoff.lean`;
- p.13 fixed-base square-sum source comparisons in
  `RegularSuspensionCoordinates.lean`;
- p.13 finite-side bounded-density adapter in
  `RegularSuspensionSquareSumIntegrability.lean`;
- supplied measurability of the fixed-base source rank stratum.

## Review

The finite-integral bridge was independently reviewed in
`review-a2-regular-suspension-local-finite-integral-bridge.md`.

## Nonclaims

No measurable-source-stratum proof, p.13 product chart, source/product
coordinate identification, proof of the uniform product-fiber loss/density
bounds, original DLN loss comparison, density/Jacobian transport,
residual positivity proof, residual-base integrability proof, normal crossing,
pole order, or RLCT extraction is proved.
