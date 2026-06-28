# Statement card - A2 Case 2 determinant-chart selected-entry chart-produced residual

## Lean target

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_chartProducedMeasure
```

## Mathematical content

For the endpoint-transported explicit Case 2 selected-entry chart, the
selected-entry weighted signed-box source measure pushed forward to the
retained-passive `TopologyTuple` determinant-chart space supports the
retained-passive p.13 residual theorem directly.

The theorem should return:

```text
(forall^ae z with respect to Measure.map chart weightedBox,
  0 < residualSquareSum (directChart z))
and
lintegral z, ofReal ((residualSquareSum (directChart z)) ^ (-t))
  with respect to Measure.map chart weightedBox < infinity.
```

## Inputs

- two-edge fixed-base data `W₂`, `B₂`, `U₀`, `hU₀`;
- finite endpoint equivalences `eNext` and `e`;
- Case 2 inequalities `hS`, `hcont`, `hnext`;
- a measurable/Borel structure on the retained-passive `TopologyTuple`;
- `0 <= t`;
- positive selected-entry radii `0 < Rres i`;
- selected-entry exponent condition
  `2 * t < ((center.erase pivotNext.1).card : ℝ) + 1`.

## Proof route

1. Reuse the already formalised Case 2 selected-entry determinant-chart
   residual theorem with supplied map identity.
2. Instantiate its ambient measure as the chart-produced measure
   `Measure.map chart weightedBox`.
3. Prove the supplied map identity from pointwise determinant-chart support of
   the endpoint-transported selected-entry chart.
4. Rewrite the theorem conclusion from the restricted chart-produced measure to
   the chart-produced measure itself.

## Nonclaims

This is not Haar measure transport.  It is not a proof that the selected-entry
image is the full retained-passive determinant chart.  It is not source-prior
identification, source-rank coverage, normal crossings, pole order, or RLCT.
