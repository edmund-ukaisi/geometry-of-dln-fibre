# Reproduction - A2 retained-passive chart-produced source-stratum bounds

Date: 2026-06-29.

Status: reproduced; Lean checked; xhigh review passed.

## Scope

This slice removes the explicit local-source pushforward hypothesis from the
retained-passive selected-entry source-stratum-bound finite-integral handoff.
The source measure is still the chart-produced selected-entry signed-box
pushforward.  Loss and density estimates are stated on the source-rank stratum,
not on the retained-passive local source.

This is independent of the quiver paper and is only a p.13 selected-entry
measure handoff.

## Pen-And-Paper Calculation

Write

```text
S = paperEndpointFixedBaseSourceRankStratum,
L = paperEndpointFixedBaseRetainedPassiveP13LocalSource.
```

Let `sourceChart` be a selected-entry chart into the retained-passive source
ambient space.  Assume pointwise chart support:

```text
sourceChart y in L.
```

Let

```text
box = Measure.pi_i volume restricted to (-R_i,R_i),
weightedBox = box.withDensity selectedEntrySourceDensity,
mu = Measure.map sourceChart weightedBox.
```

Since `sourceChart y in L` for every `y`, the pushforward measure is supported
on `L`, hence

```text
mu restricted to L = map sourceChart weightedBox.
```

This is the exact `hmap` input required by the already reproduced selected-entry
source-stratum-bound handoff.

The selected-entry residual readout is still supplied:

```text
residualSquareSum(sourceChart y)
  = selectedEntryResidual(pivot,y).
```

The selected-entry residual and source density have monomial-unit forms:

```text
selectedEntryResidual(pivot,y)
  = residualUnit(pivot,y) * prod_i |y_i|^(2*lossExp_i),
sourceDensity(pivot,y)
  = densityUnit(pivot,y) * prod_i |y_i|^(densityExp_i),
```

with

```text
1 <= residualUnit,
0 <= densityUnit <= 1.
```

Together with

```text
2*t*lossExp_i < densityExp_i + 1,
```

these give residual positivity and residual negative-power integrability on
`L` for the chart-produced measure.

The final regular-coordinate integral is over

```text
mu restricted to U cap S.
```

Loss and density bounds are therefore allowed to live on

```text
nhdsWithin x0 S.
```

The retained-passive self-base local-source coverage gives an open `Ulocal`
containing `x0` with

```text
Ulocal cap S subset Ulocal cap L.
```

The existing source-stratum-bound local-source handoff then applies with
residual hypotheses on `L` and loss/density bounds on `S`.

## Case 2 Specialization

For endpoint-transported Case 2 retained-passive data, the concrete
`sourceChart` is

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
  W2 B2 U0 hU0 (retainedData yNext).
```

The already landed Case 2 bridge supplies:

```text
sourceChart yNext in L,
sourceReadback residualFactorProduct = selectedEntry chartMap matrix.
```

The second equality gives the residual readout used above.  Thus the generic
chart-produced source-stratum-bound theorem specializes to the Case 2
endpoint-transported chart without adding source/image equality or external
source-prior transport.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** Pointwise chart support is enough to derive
the local-source pushforward identity needed by the retained-passive
source-stratum-bound selected-entry handoff, so a chart-produced measure version
can consume source-stratum loss and density bounds.

**Assumed.** Fixed-base p.13 source data, self-base continuity, selected-entry
chart support, selected-entry residual readout, positive radii, critical
selected-entry inequality, and source-stratum loss/density estimates.

**Cited.** None.

**Deferred.** Selected-entry chart image equality, source-rank coverage,
external/original source-prior transport, Jacobian comparison, analytic atlas
construction, normal crossings, pole order, and RLCT extraction.

## Lean Outcome

Implemented theorem family:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
```

Focused builds passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.  Independent
xhigh review passed in
`review-a2-retained-passive-chart-produced-source-stratum-bounds.md`.
