# Reproduction - A2 weighted signed-box residual source-measure handoff

Status: formalised and xhigh checked.

## Source Anchor

The p.13 local finite-integral bridge consumes residual source hypotheses:

```text
0 < residualSquareSum(x)  for a.e. x on the source,
int^- x, ofReal(residualSquareSum(x)^(-t)) < infinity.
```

The unweighted signed-box handoff proved these source hypotheses from a
signed-box pushforward and an unweighted threshold `2*t*k_i < 1`.  This slice
handles a supplied density/Jacobian factor on the chart side.  It assumes the
source measure is the pushforward of

```text
nu = signedBox.withDensity (fun y => ofReal(density y)),
```

and uses the existing signed-box residual/density finite-side estimate with
the Aoyagi-style inequalities `2*t*k_i < h_i + 1`.

## Calculation

Let

```text
signedBox = product_i volume.restrict (-R_i, R_i),
nu = signedBox.withDensity (fun y => ofReal(density y)),
f(y) = residualSq(chart y).
```

Assume `R_i > 0`, `c > 0`, `C >= 0`, `t >= 0`, and

```text
2*t*k_i < h_i + 1
```

for every coordinate.  Assume, for `signedBox`-almost every `y`,

```text
c * product_i |y_i|^(2*k_i) <= f(y),
0 <= density y,
density y <= C * product_i |y_i|^(h_i).
```

Finally assume the weighted source pushforward identity

```text
mu.restrict source = Measure.map chart nu.
```

The Lean theorem also assumes the measure-theoretic premises needed for this
transport: `ofReal density` is a.e.-measurable on `signedBox`, `chart` is
a.e.-measurable on `signedBox`, and the positive residual set in the source is
measurable.

### Positivity

The signed-box product measure is a.e. away from every coordinate hyperplane.
On the full-measure set where all `|y_i|` are positive and the residual lower
bound holds,

```text
0 < c * product_i |y_i|^(2*k_i) <= f(y).
```

Therefore `0 < f(y)` for `signedBox`-almost every `y`.  Since
`nu = signedBox.withDensity ...` is absolutely continuous with respect to
`signedBox`, the same positivity holds for `nu`-almost every `y`.

### Integrability

The lower-integral identity for `withDensity` gives

```text
int^- y, ofReal(f(y)^(-t)) dnu
  =
int^- y, ofReal(density y) * ofReal(f(y)^(-t)) dsignedBox.
```

On the full-measure set where `0 <= density y`, this equals

```text
int^- y, ofReal(f(y)^(-t) * density y) dsignedBox.
```

The already-landed signed-box residual/density theorem applies to the supplied
lower residual bound and upper density bound, proving this last lower integral
finite.  Its pointwise comparison is

```text
f(y)^(-t) * density y
  <= (c^(-t) * C) * product_i |y_i|^(h_i - 2*t*k_i),
```

and the finite-side product integral is finite under
`h_i - 2*t*k_i > -1`.

The existing pushforward handoff then transports chart-side positivity and
finite integral from `nu` to `mu.restrict source`.

## Lean Landing

Lean adds the weighted source-facing constructor in
`RegularSuspensionLocalMeasure.lean`:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower
```

It uses:

```text
DLNFibre.DLN.Aoyagi.lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top
MeasureTheory.withDensity_absolutelyContinuous
MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map
```

## Nonclaims

- No construction of Aoyagi's chart map.
- No proof that `mu.restrict source` is this weighted chart pushforward.
- No differentiability or Jacobian theorem.
- No construction or continuity proof for the density/prior factor.
- No original DLN loss comparison.
- No endpoint or divergent-side theorem.
- No normal-crossing production, pole order, or RLCT extraction.
