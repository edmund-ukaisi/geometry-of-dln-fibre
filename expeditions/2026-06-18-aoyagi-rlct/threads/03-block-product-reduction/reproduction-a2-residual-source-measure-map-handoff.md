# Reproduction - A2 residual source-measure map handoff

Status: formalised and xhigh checked.

## Source Anchor

The p.13 local finite-integral bridge consumes two residual source hypotheses:

```text
0 < residualSquareSum(x)  for a.e. x on the source,
int^- x, ofReal(residualSquareSum(x)^(-t)) < infinity.
```

This slice shows how to obtain exactly these two hypotheses when the restricted
source measure is explicitly supplied as a pushforward from a chart-side
measure.  It is a measure-transport handoff only: the chart map, source-measure
identity, chart-side positivity, and chart-side finite integral are all
assumptions.

## Calculation

Let

```text
residualSq(x) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap ... x).
```

Assume an a.e.-measurable chart-side map

```text
chart : beta -> alpha
```

and a measure identity

```text
mu.restrict source = Measure.map chart nu.
```

### Positivity

If the positive residual set

```text
{x | 0 < residualSq(x)}
```

is measurable and

```text
0 < residualSq(chart y)
```

for `nu`-almost every `y`, then the map identity gives

```text
0 < residualSq(x)
```

for `mu.restrict source`-almost every `x`.  In Lean this is the standard
`ae_map_iff` transport.

### Integrability

For the lower integral, it is enough to use the inequality form of change under
map:

```text
int^- x, F(x) d(Measure.map chart nu)
  <= int^- y, F(chart y) dnu.
```

Here

```text
F(x) = ofReal(residualSq(x)^(-t)).
```

Thus a finite chart-side lower integral implies

```text
int^- x, ofReal(residualSq(x)^(-t)) d(mu.restrict source) < infinity.
```

No differentiability or Jacobian formula is involved in this theorem; those
would enter in a later theorem proving the supplied map identity or bounding a
chart-side density.

## Lean Landing

Lean adds the source-measure pushforward handoff in
`RegularSuspensionLocalMeasure.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map
```

It returns the exact pair consumed by later p.13 finite-integral wrappers:

```text
residual positivity a.e.,
residualNegPowerIntegrableOn ...
```

## Nonclaims

- No construction of the chart map.
- No proof that `mu.restrict source` is a chart pushforward.
- No differentiability or Jacobian theorem.
- No density/prior transport or boundedness.
- No monomial residual lower bound.
- No original DLN loss comparison.
- No normal-crossing production, pole order, or RLCT extraction.
