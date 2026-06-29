# A2 retained-passive small-box chart-produced residual bound

## Claim

For a fixed retained-passive regular-coordinate radius `Rreg`, the residual
boundedness premise in the chart-produced selected-entry handoff follows from
the selected-entry small-box hypotheses

```text
0 <= delta,
forall i, Rres i <= delta,
delta^2 * (1 + #(center.erase pivot) * delta^2) <= Rreg^2.
```

The measure is the selected-entry weighted signed-box source measure pushed
through the retained-passive source chart and then restricted to the
retained-passive p.13 local source.  No arbitrary measure is involved.

## Pen-and-paper reproduction

Let

```text
signedBox := product_i Lebesgue|(-Rres_i,Rres_i),
sourceMeasure := signedBox.withDensity sourceDensity,
mu := sourceChart_* sourceMeasure,
localSource := retainedPassiveP13LocalSource.
```

The source-side selected-entry theorem already proves

```text
residual_pivot(y) <= Rreg^2
```

for `sourceMeasure`-a.e. `y`, provided each signed-box radius is at most
`delta` and the displayed scalar smallness inequality holds at `Rreg`.

The retained-passive readout gives, pointwise in the signed-box coordinate,

```text
squareSum(residualBlockCoordinateMap(sourceChart y))
  = residual_pivot(y).
```

Therefore the same inequality holds for the residual square-sum at
`sourceChart y`, for `sourceMeasure`-a.e. `y`.

The target set

```text
{x | squareSum(residualBlockCoordinateMap x) <= Rreg^2}
```

is measurable because the retained-passive residual-coordinate map is
measurable when `Cedge` is continuous, and `aoyagiCoordinateSquareSum` is a
measurable function of those residual coordinates.  Hence `ae_map_iff` pushes
the a.e. statement through `sourceChart`, giving it for `mu`.

Finally, the retained-passive source chart lands in `localSource`, so

```text
mu.restrict localSource = mu.
```

This transfers the same a.e. residual bound to `mu.restrict localSource`.

## Lean realisation

`RetainedPassiveLocalMeasure.lean` adds:

```text
residualSquareSum_le_sq_ae_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_of_residual_eq_of_smallBox

residualSquareSum_le_sq_ae_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure_of_smallBox

exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_of_smallBox

exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density_of_smallBox
```

The first theorem is the generic chart-produced a.e. bound from a supplied
residual readout.  The second derives the chart landing and readout from
retained-passive source-edge-family data.  The third feeds that bound into the
existing fixed-radius source-stratum two-sided handoff, replacing the explicit
residual boundedness premise by the small-box hypotheses.

The fourth theorem combines the positive continuous-density radius shrink with
the small-box residual discharge.  Its proof first obtains a radius
`R <= Rmax` from the existing continuous-density two-sided theorem.  Only after
that radius has been chosen does it ask for a `delta` satisfying

```text
0 <= delta,
forall i, Rres i <= delta,
delta^2 * (1 + #(center.erase pivot) * delta^2) <= R^2.
```

Thus the source-stratum loss bounds are still supplied at `Rmax` and then
restricted to the produced `R`, while the selected-entry residual bound is
checked at the produced radius itself.

## Boundary

The result is fixed-radius.  It does not infer a bound at a shrunken radius
from a bound at `Rmax`; when a continuous-density theorem produces a smaller
radius `R`, the small-box scalar inequality must be checked at that `R`.  The
continuous-density small-box wrapper enforces this by quantifying `delta`
after the returned `R`.

It does not choose `Rres` or `delta`, prove source-rank coverage, prove the
loss/density comparison hypotheses, identify an external source prior,
transport a Jacobian density, construct normal crossings, compute pole order,
or extract RLCT.
