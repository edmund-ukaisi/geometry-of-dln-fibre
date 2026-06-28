# Statement card - A2 retained-passive selected-entry chart-produced determinant residual

## Lean target

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_selectedEntrySignedBox_chartProducedMeasure
```

## Mathematical content

A selected-entry chart-produced determinant measure supported on the
retained-passive determinant chart satisfies the determinant-chart residual
positivity and finite negative-power integral conclusion.

This is the generic support wrapper behind the Case 2-specific chart-produced
determinant residual theorem.

## Inputs

- selected-entry center and pivot;
- a chart
  `(center -> ℝ) -> TopologyTuple ... ℝ`;
- a.e. measurability of `chart` on the unweighted signed box;
- measurability of `S = topologyTupleDetChartSet`;
- pointwise support `forall y, chart y in S`;
- measurability of the retained-passive direct residual positive set;
- positive radii, `0 <= t`, and the selected-entry exponent condition;
- residual readout
  `residualSquareSum (directChart (chart y)) =
    SelectedEntrySignedBox.CenterCoord.residual pivot y`.

## Output

For

```text
targetMeasure =
  Measure.map chart
    (signedBox.withDensity
      (fun y => ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y))),
```

the theorem returns:

```text
forall^ae z with respect to targetMeasure,
  0 < residualSquareSum (directChart z)
```

and

```text
lintegral z, ofReal ((residualSquareSum (directChart z)) ^ (-t))
  with respect to targetMeasure < infinity.
```

## Nonclaims

This is not an arbitrary-measure theorem.  It does not identify Haar measure or
an external source prior, prove that the chart image is all of the determinant
chart, prove source-rank coverage, construct normal crossings, compute pole
order, or extract RLCT.
