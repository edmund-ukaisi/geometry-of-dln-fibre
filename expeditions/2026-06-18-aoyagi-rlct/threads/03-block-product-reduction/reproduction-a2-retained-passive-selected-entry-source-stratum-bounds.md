# Reproduction - A2 retained-passive selected-entry source-stratum bounds

Date: 2026-06-29.

Status: reproduced; Lean target landed.

## Scope

This slice specializes the source-stratum-bound local-source finite-integral
bridge to the retained-passive selected-entry signed-box residual chart.

The previous retained-passive selected-entry handoff required the loss lower
bound and density bounds on

```text
nhdsWithin x0 retainedPassiveP13LocalSource.
```

The p.13 comparison estimates are naturally produced on the source-rank
stratum.  The new theorem keeps the selected-entry residual chart and
pushforward hypotheses unchanged, but accepts the loss and density bounds on

```text
nhdsWithin x0 sourceStratum.
```

It then uses the retained-passive determinant-chart neighborhood inclusion to
connect the two source sets.

## Pen-And-Paper Calculation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum,
L = paperEndpointFixedBaseRetainedPassiveP13LocalSource.
```

The selected-entry chart data provide a signed-box source measure and a map
`sourceChart` with the supplied pushforward identity

```text
mu restricted to L = map sourceChart signedBoxWithDensity.
```

The residual readout says

```text
residualSquareSum(sourceChart y)
  = selectedEntryResidual(pivot,y).
```

The selected-entry residual has the elementary monomial-unit form

```text
selectedEntryResidual(pivot,y)
  = residualUnit(pivot,y) * prod_i |y_i|^(2*lossExp_i),
```

with `1 <= residualUnit`.  The selected-entry source density has the form

```text
sourceDensity(pivot,y)
  = densityUnit(pivot,y) * prod_i |y_i|^(densityExp_i),
```

with `0 <= densityUnit <= 1`.  Together with

```text
2*t*lossExp_i < densityExp_i + 1
```

these are exactly the monomial integrability hypotheses for residual
positivity and residual negative-power integrability on `L`.

Independently, since the fixed-base edge family is continuous and equals the
self-base edge family at `x0`, the retained-passive determinant-chart local
source is a neighborhood of `x0`.  Hence there is an open `Ulocal` containing
`x0` such that

```text
Ulocal cap S subset Ulocal cap L.
```

Now assume the p.13 regular-coordinate loss and density bounds on `S`:

```text
creg * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),
0 <= density(x,u),
density(x,u) <= Creg.
```

The general source-stratum-bound local-source handoff applies with this
coverage inclusion and the residual hypotheses on `L`.  It returns an open
neighborhood `U` of `x0` such that the regular-coordinate finite integral over

```text
mu restricted to U cap S
```

is finite.

## Lean Landing

The landed theorem is in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds
```

It uses:

```text
signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource
```

## Boundary Checks

- The theorem consumes the selected-entry source-measure pushforward `hmap`;
  it does not identify an external or original source prior.
- The theorem consumes the selected-entry residual readout; it does not prove a
  selected-entry chart image equality.
- The coverage used is only the retained-passive determinant-chart local-source
  inclusion near the self-base point.
- No source-rank coverage by selected-entry charts is proved.
- No Jacobian/prior transport, analytic atlas, normal crossings, pole order, or
  RLCT extraction is proved.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** The retained-passive selected-entry
finite-integral handoff with supplied `hmap` and residual readout can consume
loss/density bounds on the source-rank stratum instead of on the retained-
passive local source.

**Assumed.** Fixed-base source data, continuous edge family at self-base,
selected-entry signed-box source chart measurability, local-source pushforward
identity, positive selected-entry radii, the selected-entry critical inequality,
residual readout, and source-stratum loss/density bounds.

**Cited.** None.

**Deferred.** Chart-produced no-`hmap` source-stratum-bound wrapper; selected-
entry chart image equality; original source-prior transport; Jacobian
comparison; normal crossings; pole order; and RLCT extraction.
