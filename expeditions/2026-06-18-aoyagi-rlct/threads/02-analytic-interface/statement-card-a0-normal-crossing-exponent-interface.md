# Statement card - A0 normal-crossing exponent interface

## Claim

Given finite normal-crossing exponent data from a supplied analytic chart
certificate, the Aoyagi exponent minimum and order count are well-defined
finite objects:

```text
lambda_exp = min_{chart, j : k_{chart,j} > 0} (h_{chart,j}+1)/(2 k_{chart,j}),
theta_exp  = max_chart Card { j : k_{chart,j} > 0 and
                              (h_{chart,j}+1)/(2 k_{chart,j}) = lambda_exp }.
```

The analytic theorem identifying external RLCT data with these finite objects
is not proved; it is represented by an explicit hypothesis.

## Lean names

File: `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`.

- `AoyagiNormalCrossingExponentData`
- `AoyagiNormalCrossingExponentData.activePairs`
- `AoyagiNormalCrossingExponentData.ratioAt`
- `AoyagiNormalCrossingExponentData.activeRatios`
- `AoyagiNormalCrossingExponentData.exponentMinimum`
- `AoyagiNormalCrossingExponentData.minCoordsInChart`
- `AoyagiNormalCrossingExponentData.minCountInChart`
- `AoyagiNormalCrossingExponentData.chartMinCounts`
- `AoyagiNormalCrossingExponentData.exponentOrder`
- `AoyagiNormalCrossingExtractionHypothesis`

Helper theorems include active/minimum nonemptiness, existence of an active
minimum coordinate, existence of an order-attaining chart, and
`one_le_exponentOrder`.

## Status

Proved in Lean as finite arithmetic/interface infrastructure.

## Assumptions

The data assumes at least one active coordinate with positive loss exponent.
The extraction hypothesis separately assumes the analytic normal-crossing
certificate and the cited theorem.

## Explicit exclusions

No analytic resolution theorem, chart construction, unit nonvanishing proof,
ideal-generator invariance, regular-coordinate additivity, deepest-point
comparison, pole-order theorem, or RLCT theorem is proved here.
