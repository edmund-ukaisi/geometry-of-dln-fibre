# Reproduction - A2 Case 2 determinant-chart selected-entry residual handoff

Date: 2026-06-28.

Status: controller pen-and-paper reproduction before Lean.  This is the Case 2
specialization of the retained-passive selected-entry determinant-chart
residual handoff.

## Shape

In the two-edge Case 2 lane we have explicit successor selected-entry
coordinates

```text
yNext : center -> R
center = case2ResidualBlockPivotEntries n S (J + 1)
pivotNext = (J + 2, J + 2) in center.
```

The endpoint-transported retained-passive determinant-chart datum is

```text
retainedData(yNext) =
  (case2PostPivotSelectedEntryRetainedPassiveData
    n hS hcont hnext yNext eNext).endpointTransport e.
```

The determinant-chart coordinate map to be used in the generic handoff is

```text
chart(yNext) = topologyTuple (retainedData(yNext)).
```

Since the Case 2 datum is in the determinant chart and endpoint transport
preserves determinant-chart membership, `chart(yNext)` lies in the retained
passive determinant chart.  For the generic residual handoff, however, the
needed measure fact is still the supplied pushforward identity

```text
m.restrict topologyTupleDetChartSet =
  Measure.map chart
    (signedBox.withDensity
      (fun y => ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))).
```

This note does not prove that pushforward identity.

## Calculation

The generic retained-passive selected-entry determinant-chart theorem needs
three Case 2 inputs.

First, `chart` is a.e. measurable on the signed box.  This follows from
continuity:

```text
yNext |-> case2PostPivotSelectedEntryRetainedPassiveData ... yNext eNext
```

is continuous, endpoint transport is continuous, and `topologyTuple` is
continuous.  Thus their composition `chart` is continuous and therefore
a.e. measurable.

Second, the generic theorem needs a residual readout:

```text
residualSquareSum (directChart (chart yNext)) =
  SelectedEntrySignedBox.CenterCoord.residual pivotNext yNext.
```

Here

```text
directChart(z) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (ofTopologyTuple z).
```

For `z = chart yNext = topologyTuple (retainedData yNext)`,
`ofTopologyTuple (topologyTuple (retainedData yNext)) = retainedData yNext`.
Therefore `directChart (chart yNext)` is exactly the fixed-base source edge
family attached to the endpoint-transported Case 2 data.  The existing Case 2
readout theorem gives

```text
aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap
    W2 B2 U0 hU0 id
    (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
      W2 B2 U0 hU0 (retainedData yNext)))
 =
SelectedEntrySignedBox.CenterCoord.residual pivotNext yNext.
```

Third, the generic theorem still needs the target positive-set measurability

```text
MeasurableSet {z | 0 < residualSquareSum (directChart z)}.
```

This is measure-theoretic bookkeeping separate from the selected-entry
positivity/integrability calculation, so the Case 2 specialization keeps it as
an explicit hypothesis.

With those inputs, the generic theorem transports the selected-entry
weighted-box theorem through the supplied determinant-chart pushforward
identity and concludes

```text
for m.restrict topologyTupleDetChartSet-a.e. z,
  residualSquareSum (directChart z) > 0,

integral^- ofReal (residualSquareSum (directChart z)^(-t))
  d(m.restrict topologyTupleDetChartSet) < infinity.
```

## Lean target

Add in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

a theorem with content:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map
```

It should discharge the selected-entry chart a.e. measurability and residual
readout, while keeping the determinant-chart pushforward identity and target
positive-set measurability explicit.

## Boundary

This is a two-edge Case 2 specialization only.  It does not construct endpoint
equivalences, prove the determinant-chart pushforward identity, prove chart
coverage, identify an original external source prior, prove local loss or
density bounds, prove source-rank coverage, construct normal crossings,
compute pole order, or extract an RLCT.
