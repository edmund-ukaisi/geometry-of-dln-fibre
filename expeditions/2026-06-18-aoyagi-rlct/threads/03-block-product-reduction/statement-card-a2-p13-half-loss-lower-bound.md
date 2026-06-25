# Statement Card - A2 p.13 half loss lower bound

## Statement

On the fixed-base source-rank stratum filter, the literal p. 13
product-difference square-sum is eventually bounded below by one half of the
regular-plus-residual cleaned square-sum:

```text
(1/2) * (regularSquareSum + residualSquareSum) <= literalSquareSum.
```

If a supplied ambient loss satisfies

```text
c * literalSquareSum <= loss
```

eventually on the same filter with `c >= 0`, then

```text
(c/2) * (regularSquareSum + residualSquareSum) <= loss.
```

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source_of_rank_eq
```

## Source

Aoyagi p. 13 product-difference display and the already formalised finite
literal/cleaned square-sum comparison for that display.

## Dependencies

- `literal_regular_add_residual_squareSum_eventually_factor_two_nhdsWithin_source`;
- ordered arithmetic over `ℝ`;
- source-rank fixed-base regular-coordinate source data.

## Nonclaims

No original-loss comparison, analytic chart construction, Jacobian/prior
transport, regular-suspension theorem, normal crossings, pole order, or RLCT
extraction is proved.
