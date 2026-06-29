# Statement Card - A2 Retained-Passive Passive-Variable Sector Transport

Status: reviewed specification; first Lean readout subtarget landed separately.

Reproduction:

```text
reproduction-a2-retained-passive-passive-variable-sector-transport.md
```

Review:

```text
review-a2-retained-passive-passive-variable-sector-transport.md
```

## Claim

A source-measure theorem at the current Case 2 frontier must use a
passive-variable-explicit sector.  The coordinate domain is the product of the
retained passive matrix variables and the selected-entry residual coordinates.
The selected-entry residual chart is invertible only on a nonzero-pivot
sector, while its pivot-zero locus is handled only by a.e. or finite-integral
arguments.

The current passive selected-entry finite-integral theorems use a
chart-produced measure.  They do not prove determinant-chart Haar transport or
comparison with an external/original DLN source prior.

## Source Basis

Aoyagi pp. 10-13 support:

```text
F2 = -A1^{-1} A2
F3 = -A3 A1^{-1}
C4 = -A3 A1^{-1} A2 + A4
```

and the p.13 product-difference block

```text
[ C1 - Er              -F2
  -F3       prod_s C^(s) - F3 F2 ].
```

They do not state selected-entry determinant-chart coverage, passive-sector
Haar transport, or original source-prior comparison.

## Existing Lean Inputs

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq
exists_open_measure_map_case2EndpointTransport_withPassive_withDensity_restrict_retainedPassiveP13LocalSource_eq_self
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap
SelectedEntrySignedBox.CenterCoord.chartMap_preimageOfPivotNeZero
SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
```

## Next Lean Subtarget

The first Lean-ready subtarget was not a measure equality.  It was the combined
with-passive open punctured-sector inverse/readout package:

```text
for (theta,y) in the determinant sector with y pivotNext != 0,
  sourceReadback(sourceChart(theta,y)) = data(theta,y)
  and selected-entry inverse of the residual readout recovers y.
```

This should package existing ingredients: the with-passive open source-readback
theorem, the with-passive endpoint residual-factor chart-map identity, and
`SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap`, using the
existing passive pointwise chart-map readout theorem or its residual-factor
identity as the implementation bridge.  The non-passive punctured readout
package already exists; the missing piece is the passive-variable open-sector
version.

This subtarget is now tracked separately at:

```text
statement-card-a2-retained-passive-open-punctured-sector-readout.md
```

## Later Measure Targets

A later transport theorem must choose one precise target:

```text
chart-produced passive sector measure
determinant-chart Haar restricted to a sector image
external/original source-prior comparison
```

Only the first is currently represented by the passive Case 2 finite-integral
theorems.

## Nonclaims

No passive-sector Haar theorem, source-prior transport, selected-entry
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT extraction is proved by this card.
