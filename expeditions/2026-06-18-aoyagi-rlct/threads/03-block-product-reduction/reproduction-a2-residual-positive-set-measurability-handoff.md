# Reproduction - A2 residual positive-set measurability handoff

Date: 2026-06-25.

Status: pen-and-paper reproduction for a small residual-source measure
handoff.

## Source Anchor

The p.13 residual-source constructors use the positive residual set

```text
{x | 0 < residualSquareSum(x)}
```

as the target event in the source-measure pushforward argument.  The existing
weighted signed-box handoff proves chart-side residual positivity and finite
residual negative-power integrability, but still asks the caller to supply
measurability of this source positive set.

This slice removes that supplied event-measurability premise when the residual
coordinate map itself is measurable.

## Calculation

Let

```text
coord(x) =
  paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 Cedge x
```

and

```text
residualSquareSum(x) = aoyagiCoordinateSquareSum(coord(x)).
```

For a finite coordinate index `eta`,

```text
aoyagiCoordinateSquareSum(y) = sum_i y_i^2.
```

If `coord : alpha -> eta -> R` is measurable, then each scalar coordinate
`x |-> coord(x)_i` is measurable.  Therefore `x |-> coord(x)_i * coord(x)_i`
is measurable, and the finite sum over `i` is measurable.  Hence

```text
residualSquareSum : alpha -> R
```

is measurable.  Since `(0, infinity)` is Borel measurable,

```text
{x | 0 < residualSquareSum(x)}
```

is measurable as the preimage of `(0, infinity)`.

The weighted signed-box residual constructor can therefore derive its
`hpos_meas` input from a measurable residual coordinate map and then call the
existing theorem unchanged.

## Boundaries

This is not a proof that Aoyagi's residual coordinate map is globally
measurable from the edge-family data.  That stronger result would require
checking measurability through the deterministic suffix-state recursion,
matrix inverse on determinant charts, and every finite block operation.

This handoff also does not prove residual positivity, residual integrability,
chart construction, source-measure pushforward, Jacobian/density transport,
original-loss comparison, normal crossings, pole order, or RLCT extraction.

## Kill Conditions

- If only centered `ContinuousAt` data are available, do not use this theorem:
  it requires a global measurability hypothesis for the residual coordinate
  map.
- Do not replace the chart-side monomial lower bound or weighted pushforward
  hypotheses with this theorem; it supplies only the target-event measurability
  needed by the pushforward positivity step.
- Do not name the theorem as if it constructs the p.13 chart or residual
  source hypotheses by itself.
