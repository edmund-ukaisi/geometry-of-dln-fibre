# Reproduction - A2 signed-box residual source-measure handoff

Status: formalised and xhigh checked.

## Source Anchor

The p.13 local finite-integral bridge consumes residual source hypotheses:

```text
0 < residualSquareSum(x)  for a.e. x on the source,
int^- x, ofReal(residualSquareSum(x)^(-t)) < infinity.
```

The previous source-measure map handoff proved that these hypotheses transport
from a supplied chart-side measure.  This slice supplies one elementary
chart-side sufficient condition: an unweighted signed-box product measure and
an a.e. absolute-monomial lower bound for the residual square.

## Calculation

Let `I` be finite and set

```text
nu = product_i volume.restrict (-R_i, R_i),  with R_i > 0.
```

Write

```text
f(y) = residualSq(chart y).
```

Assume `c > 0`, `t >= 0`, `k_i : Nat`, and

```text
c * product_i |y_i|^(2*k_i) <= f(y)
```

for `nu`-almost every `y`.  Assume also the strict unweighted finite-side
conditions

```text
2*t*k_i < 1
```

for every coordinate.

### Positivity

For the signed-box product measure, every coordinate hyperplane has measure
zero.  Hence

```text
0 < |y_i|
```

for every `i`, for `nu`-almost every `y`.  On the intersection with the
full-measure set where the lower bound holds,

```text
0 < product_i |y_i|^(2*k_i),
0 < c * product_i |y_i|^(2*k_i) <= f(y).
```

Therefore `0 < residualSq(chart y)` for `nu`-almost every `y`.

### Integrability

On the same full-measure set, because `t >= 0`,

```text
f(y)^(-t)
  <= c^(-t) * product_i |y_i|^(-2*t*k_i).
```

The product integral factors into the one-dimensional finite-side integrals

```text
int_{-R_i}^{R_i} |u|^(-2*t*k_i) du,
```

which are finite under `2*t*k_i < 1`.  Thus

```text
int^- y, ofReal(f(y)^(-t)) dnu < infinity.
```

Combining this chart-side positivity and finite integral with the previously
landed pushforward handoff gives the residual source hypotheses when

```text
mu.restrict source = Measure.map chart nu.
```

## Edge Cases

- If `t = 0`, the negative-power integrand is `1`; the signed box has finite
  product measure.
- If `k_i = 0`, the corresponding factor is `1`, and `2*t*k_i < 1` is
  automatic.
- If the index type is empty, the empty product is `1`, the lower bound is
  `c <= f` a.e., and the empty product measure is finite.

## Lean Landing

Lean adds the density-free signed-box integrability theorem in
`MonomialChartIntegrability.lean`:

```text
DLNFibre.DLN.Aoyagi.lintegral_ofReal_loss_rpow_neg_signedBox_lt_top
```

and the source-facing constructor in `RegularSuspensionLocalMeasure.lean`:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_monomialLower
```

The source-facing theorem first derives chart-side residual positivity from
the signed-box nonzero-coordinate a.e. fact, then derives chart-side finite
integral from the density-free signed-box theorem, and finally delegates to
the already-landed pushforward handoff.

## Nonclaims

- No construction of Aoyagi's chart map.
- No proof that `mu.restrict source` is a chart pushforward.
- No differentiability, Jacobian formula, or density/prior transport.
- No density-weighted Aoyagi exponent inequality `2*t*k_i < h_i+1`; this
  unweighted constructor uses the stricter `2*t*k_i < 1`.
- No original DLN loss comparison.
- No normal-crossing production, pole order, or RLCT extraction.
