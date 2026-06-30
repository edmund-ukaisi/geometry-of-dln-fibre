# Statement Card - A2 Case 2 product source chart small-ball readout

## Claim

For the concrete Case 2 full p.13 product source chart, there is a positive
regular-coordinate radius `R <= Rmax` such that, eventually along the base
source-rank stratum and for every `u in ball 0 R`, the product chart reads out
regular coordinates as `u` and residual coordinates as the underlying
passive-theta source residual coordinates.

Public Lean name:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq_nhdsWithin_source
```

## Inputs Used

- the concrete passive-theta endpoint source chart;
- a base point `theta0`;
- a source-rank stratum `paperEndpointFixedBaseSourceRankStratum ... r rEdge`;
- a positive radius cap `Rmax`;
- the generic small-ball product-coordinate readout theorem specialized at
  `M := 0`.

## Output

Lean returns `R > 0`, `R <= Rmax`, and the two eventual readout facts:

```text
eventually theta in nhdsWithin theta0 sourceStratum,
  forall u in ball 0 R,
    regular(productSourceChart(theta,u)) = u

eventually theta in nhdsWithin theta0 sourceStratum,
  forall u in ball 0 R,
    residual(productSourceChart(theta,u)) = residual(sourceChart theta)
```

## Proof Shape

Apply

```text
exists_pos_radius_le_regular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily_nhdsWithin_source
```

with `M := 0`, `V := W2`, `Bv := B2`, and
`CedgeBase := case2PassiveThetaEndpointSourceChart ...`.

## Nonclaims

This is not source-image coverage and not a full product-chart inverse.  It
does not prove original/source-prior transport, Haar transport, normal
crossings, pole order, or RLCT extraction.
