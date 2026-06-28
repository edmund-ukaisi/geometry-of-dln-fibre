# Reproduction - A2 Case 2 inverse-Jacobian residual-source handoff

Date: 2026-06-28.

Status: controller pen-and-paper reproduction before Lean.  This is a
composition of the Case 2 determinant-chart selected-entry residual handoff
with the raw-order retained-passive inverse-Jacobian residual-source socket.

## Shape

In the two-edge Case 2 lane, the endpoint-transported selected-entry chart is

```text
chart(yNext) =
  topologyTuple
    ((case2PostPivotSelectedEntryRetainedPassiveData
      n hS hcont hnext yNext eNext).endpointTransport e),
```

with

```text
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2) in center.
```

The determinant-chart residual theorem already proved for this chart states
that, if the supplied determinant-chart pushforward identity and target
positive-set measurability hold, then the direct retained-passive residual

```text
residual(z) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap
      W2 B2 U0 hU0 id (directChart z))
```

is positive for `m.restrict Sdet`-a.e. `z` and has finite negative-power
lower integral over `m.restrict Sdet`.

The raw-order inverse-Jacobian residual-source socket uses the same
determinant-chart set

```text
Sdet = topologyTupleDetChartSet
```

and the same direct chart

```text
directChart(z) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (ofTopologyTuple z).
```

It then defines the raw-order source measure

```text
T = topologyTupleRawOrderSourceRecursiveDetChartSet,
rawChart =
  paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W2 B2 U0 hU0,
invJacDensity(y) =
  ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y),
mu = Measure.map rawChart ((m.restrict T).withDensity invJacDensity).
```

The target source set is the identity retained-passive local source

```text
localSource =
  paperEndpointFixedBaseRetainedPassiveP13LocalSource W2 B2 U0 hU0 id.
```

## Calculation

The composition has one mathematical step.  Apply the Case 2 determinant-chart
selected-entry residual theorem with the supplied hypotheses:

```text
m.restrict Sdet =
  Measure.map chart
    (signedBox.withDensity
      (fun y => ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))),

MeasurableSet {z | 0 < residual(z)},
0 <= t,
forall i, 0 < Rres i,
2 * t < ((center.erase pivotNext.1).card : R) + 1.
```

It returns

```text
hpos_chart :
  for m.restrict Sdet-a.e. z, residual(z) > 0,

hfinite_chart :
  integral^- ofReal (residual(z)^(-t)) d(m.restrict Sdet) < infinity.
```

The raw-order inverse-Jacobian residual-source wrapper

```text
residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
```

requires exactly `hpos_chart` and `hfinite_chart`.  Its internal work is the
previously proved source-measure transport and source-space positive-set
measurability for the identity source family.  Therefore it concludes

```text
for mu.restrict localSource-a.e. x, residual(x) > 0,

residualNegPowerIntegrableOn id localSource mu t.
```

No additional Jacobian calculation is performed in this composition.  The
inverse-Jacobian density and raw-order chart are inherited from the socket.

## Lean target

Add in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

a theorem with content:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
```

The theorem should first call

```text
retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map
```

and then feed the resulting pair into

```text
residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide.
```

The same composition also gives the finite-integral consumer.  Use the same
first step and then call

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide.
```

This second theorem must additionally expose `sourceData`, `[SFinite m]`, the
regular-coordinate Haar measure `nu`, `loss`, `density`, positive `R`, positive
`c`, nonnegative `C`, positive `t`, and the local loss lower bound plus density
nonnegativity and upper-bound hypotheses.

## Boundary

This is a Case 2 composition theorem.  It does not prove the determinant-chart
pushforward identity, target positive-set measurability, chart coverage,
original external source-prior transport, local loss or density bounds,
source-rank coverage, normal crossings, pole order, or RLCT extraction.
