# A2 Case 2 Inverse-Jacobian Density-Continuous Finite Integral

## Claim

In the two-edge Case 2 endpoint-transport lane, the raw-order
inverse-Jacobian finite-integral theorem can replace supplied local density
nonnegativity and upper-bound hypotheses by positive continuity of the density
at the fixed-base regular-coordinate center.

The determinant-chart pushforward identity remains explicit:

```text
m.restrict Sdet = Measure.map chart weightedBox.
```

The local loss lower bound also remains explicit, now on a prescribed radius
`Rmax`.

## Objects

Use the existing Case 2 raw-order inverse-Jacobian source measure

```text
mu =
  Measure.map rawChart
    ((m.restrict T).withDensity inverseJacobianDensity),
```

where

```text
Sdet = topologyTupleDetChartSet,
T = topologyTupleRawOrderSourceRecursiveDetChartSet,
rawChart = paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart,
inverseJacobianDensity z =
  ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity z).
```

The regular-coordinate center is

```text
base p = LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p),
u = 0 in EuclideanSpace ℝ rhoReg.
```

## Reproduction

Assume

```text
ContinuousAt density (base, 0),
0 < density (base, 0),
0 < Rmax.
```

The general local-measure helper

```text
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
```

applied with `s = localSource` gives radii and a bound

```text
exists R C,
  0 < R,
  R <= Rmax,
  0 <= C,
  eventually in nhdsWithin base localSource:
    forall u in ball 0 R, 0 <= density (x,u),
  eventually in nhdsWithin base localSource:
    forall u in ball 0 R, density (x,u) <= C.
```

The supplied loss lower bound is assumed on `ball 0 Rmax`:

```text
eventually x in nhdsWithin base localSource,
  forall u in ball 0 Rmax,
    c * (residualSquareSum x + |u|^2) <= loss (x,u).
```

Since `R <= Rmax`, `Metric.ball_subset_ball` restricts this same loss lower
bound to `ball 0 R`.

Now all hypotheses of the existing theorem

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
```

are available with radius `R` and density bound `C`.  Applying it gives an open
neighborhood `U` of `base` and the finite lower integral over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

with the exponent shifted by the regular-variable count.  The wrapper returns
`R`, `C`, and `U`, together with `0 < R`, `R <= Rmax`, `0 <= C`, openness,
base membership, and the finite-integral conclusion.

## Boundary

This theorem is a local density-bound wrapper.  It does not prove the
determinant-chart pushforward identity, construct the source measure from an
external/original prior, prove chart coverage, prove source-rank coverage,
construct normal crossings, compute pole order, or extract RLCT.
