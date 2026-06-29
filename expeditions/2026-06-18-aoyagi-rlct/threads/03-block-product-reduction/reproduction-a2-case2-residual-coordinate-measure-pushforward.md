# Reproduction - A2 Case 2 residual-coordinate measure pushforward

Date: 2026-06-29.

Status: pen-and-paper reproduction for a chart-produced measure transport
inside the retained-passive Case 2 lane.

## Question

For the endpoint-transported continuing Case 2 selected-entry chart, what is
the pushforward of the chart-produced source measure by the fixed-base
residual-coordinate map?

Answer: it is exactly Lebesgue measure restricted to the selected-entry chart
image.  This is a chart-produced residual-coordinate statement.  It is not an
external source-prior statement.

## Source Calculation

Let `center` be the successor residual block center and let `pivotNext` be the
displayed pivot `(J+2,J+2)`.  Aoyagi's Case 2 blow-up writes the residual
center chart as

```text
value = chartMap pivotNext yNext.
```

In the endpoint-transported retained-passive p.13 source chart, the already
proved fixed-base residual-coordinate readout is

```text
residualBlockCoordinateMap (sourceChart yNext) c
  = chartMap pivotNext yNext (residualCoordEquiv c).
```

Therefore, after reindexing residual coordinates by `residualCoordEquiv.symm`,

```text
residualMap (sourceChart yNext) = chartMap pivotNext yNext.
```

The selected-entry finite chart already proves the weighted pushforward

```text
Measure.map (chartMap pivotNext)
  ((signedBoxMeasure Rres).withDensity sourceDensity)
= volume.restrict (chartMap pivotNext '' signedBoxSet Rres).
```

Composing these two facts gives the desired source-side statement:

```text
Measure.map residualMap
  (Measure.map sourceChart sourceMeasure)
= volume.restrict (chartMap pivotNext '' signedBoxSet Rres).
```

## Lean Target

Add in `RetainedPassiveCase2LocalJacobianMeasure.lean`:

```text
measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_eq_restrict_chartMap_image
```

The proof combines:

```text
continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData
SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix
```

An intermediate deterministic fixed-pivot inverse wrapper was considered and
reviewed as mathematically safe, but was not kept: the existing existential
punctured value theorem already exposes the same witness when needed, and this
slice should stay centered on the measure transport.

## Nonclaims

No selected-entry source coverage, source-rank coverage, source/image
equality, original source-prior transport, ambient Jacobian comparison,
analytic atlas construction, normal crossings, pole order, or RLCT is proved.
The source measure is the chart-produced pushforward measure.
