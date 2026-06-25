# Reproduction - A2 continuous density local bounds

Status: formalised and xhigh checked.

## Source Anchor

The p.13 local finite-integral bridge consumes three analytic inputs:

```text
loss lower bound,
0 <= density,
density <= C.
```

This slice only moves the last two when the transported density factor is
already supplied as a positive continuous function at the product-chart
center.  It does not construct the chart, compute the Jacobian, prove the
Jacobian/prior formula, or compare the original DLN loss.

## Calculation

Let `density : α × E -> R` be continuous at `(x0,0)` and suppose

```text
0 < density (x0,0).
```

Choose

```text
C = density (x0,0) + 1.
```

Then `density (x0,0)` lies in the open interval `(0,C)`.  Continuity gives a
product neighborhood `U × V` of `(x0,0)` on which

```text
0 < density (x,u) < C.
```

Given any positive radius cap `Rmax`, choose `R <= Rmax` with
`ball(0,R) ⊆ V`.  Then for all `x` eventually near `x0` and all
`u ∈ ball(0,R)`,

```text
0 <= density (x,u),
density (x,u) <= C.
```

The source-relative version is the same statement after weakening from
`nhds x0` to `nhdsWithin x0 sourceStratum`.

## Residual Restriction Plumbing

The final local finite-integral theorem also shrinks the source set from the
whole source stratum to `U ∩ sourceStratum`.  Residual positivity and residual
negative-power integrability are monotone under this restriction:

```text
μ.restrict (U ∩ sourceStratum) <= μ.restrict sourceStratum.
```

Thus a.e. positivity transfers by `ae_mono`, and lower-integral finiteness
transfers by monotonicity of the measure in `lintegral_mono'`.

This is only restriction plumbing.  It does not prove the original residual
positivity/integrability hypotheses.

## Lean Landing

Lean adds the generic density bound in `LocalMeasureHandoff.lean`:

```text
exists_pos_radius_le_eventually_density_bounds_of_continuousAt_pos
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
```

Lean adds the residual restriction helper and p.13 consumer in
`RegularSuspensionLocalMeasure.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_mono
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density
```

The consumer returns a smaller radius `R`, a bound `C`, and an open source
neighborhood `U` for the existing finite-integral conclusion.  The loss lower
bound is still supplied, but only at the larger radius cap `Rmax`; it is
restricted to the smaller radius by `ball_subset_ball`.

## Nonclaims

- No Aoyagi product chart is constructed.
- No Jacobian or prior-density formula is proved.
- No transport of a source measure through a chart is proved.
- No original DLN loss comparison is proved.
- No residual positivity or residual negative-power integrability is proved.
- No normal-crossing chart certificate, pole order, or RLCT conclusion is
  obtained.
