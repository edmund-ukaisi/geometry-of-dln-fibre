# Reproduction - A2 Case 2 passive-theta endpoint reference

Date: 2026-07-01.

Status: pen-and-paper reproduction for the concrete passive-theta reference
measure and its determinant-chart support after determinant-sector
localization.

## Question

In the full Case 2 passive-theta coordinate domain, name the coordinate-product
reference measure that should replace an arbitrary `passiveMeasure`, and record
the first support statement it satisfies after localization in the determinant
sector.

## Coordinates

The full passive-theta coordinate is

```text
theta = (A1passive, F2, A3passive, Ctop, F3, yNext).
```

The passive fields are

```text
A1passive : Fin 1 -> Matrix rho rho R
F2        : Fin 2 -> Matrix rho kappa_p R
A3passive : Fin 1 -> Matrix kappa_{p+1} rho R
Ctop      : Matrix rho rho R
F3        : Matrix kappa_2 rho R.
```

The residual center coordinate is

```text
yNext : center -> R,
center = case2ResidualBlockPivotEntries n S (J+1),
pivotNext = (J+2,J+2) in center.
```

The selected-entry center chart is the elementary blow-up chart

```text
chi_y(pivotNext) = yNext(pivotNext),
chi_y(q)         = yNext(pivotNext) * yNext(q), q != pivotNext.
```

The punctured selected-entry condition is `yNext(pivotNext) != 0`.  It is not
needed for determinant-chart support, but it is needed for inverse readout and
source-chart statements.

## Reference Measure

The passive-field reference is the product of entrywise Lebesgue measures on
each passive matrix block:

```text
dA1passive dF2 dA3passive dCtop dF3.
```

In Lean this is not written as bare `volume`, because the ambient
measurable-space instance for the nested product is the product/Pi measurable
space used throughout the passive-theta files.  The definition therefore names
the entrywise product measure explicitly:

```text
matrixEntryReferenceMeasure m n
  = Measure.pi (fun _ : m => Measure.pi (fun _ : n => volume)).
```

The center reference is the selected-entry weighted signed-box measure

```text
signedBox.withDensity
  (fun y => ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)).
```

Thus the concrete full passive-theta reference source is

```text
case2PassiveThetaReferenceSourceMeasure
  = passiveFieldReference.prod centerWeightedBox.
```

This measure includes the passive fields suppressed by the reduced
selected-entry section.  It is not the reduced selected-entry source measure
alone.

The corresponding endpoint image measure is named as

```text
case2PassiveThetaEndpointReferenceImageMeasure
  = Measure.map Y ((case2PassiveThetaReferenceSourceMeasure).restrict Omega).
```

This name is meant to prevent a false replacement by unrestricted
determinant-chart Haar.

## Determinant Support

The endpoint topology-tuple map is

```text
Y(theta) = topologyTuple(endpointTransport_e(data0(theta))),
```

where `data0(theta)` keeps the passive fields and builds the residual center
matrix family from `yNext`.

The determinant sector is

```text
case2PassiveThetaDetSector
  = {theta | IsUnit theta.Ctop.det
      and forall p : Fin 1, IsUnit ((theta.A1passive p).det)}.
```

Only `Ctop` and `A1passive` enter determinant-chart membership.  The variables
`F2`, `A3passive`, `F3`, and `yNext` do not.

Therefore if `Omega` is measurable and

```text
Omega subset case2PassiveThetaDetSector,
```

then for every `theta in Omega`,

```text
Y(theta) in topologyTupleDetChartSet.
```

By a.e. support transfer through `Measure.map`, the concrete reference source
satisfies

```text
(Measure.map Y ((case2PassiveThetaReferenceSourceMeasure).restrict Omega))
    .restrict topologyTupleDetChartSet
  =
Measure.map Y ((case2PassiveThetaReferenceSourceMeasure).restrict Omega).
```

Equivalently, the named endpoint image measure satisfies

```text
(case2PassiveThetaEndpointReferenceImageMeasure ... Omega).restrict
    topologyTupleDetChartSet
  =
case2PassiveThetaEndpointReferenceImageMeasure ... Omega.
```

If another passive-field measure is dominated by a scalar multiple of the
coordinate passive-field reference,

```text
passiveMeasure
  <= d • case2PassiveThetaPassiveFieldReferenceMeasure,
```

then after taking product with the same weighted center box, restricting to
`Omega`, and pushing through `Y`, the result is dominated by the named endpoint
reference image measure:

```text
Measure.map Y ((passiveMeasure.prod weightedBox).restrict Omega)
  <= d • case2PassiveThetaEndpointReferenceImageMeasure ... Omega.
```

This is the image-measure replacement for the false unrestricted full-Haar
target.

## Boundary

This does not prove a change-of-variables theorem for `Y`.  The square
Jacobian already formalized in the retained-passive files belongs to the full
topology-tuple raw-order map

```text
Phi = topologyTupleEdgeRawOrder,
```

not to the passive-theta endpoint map `Y` alone.  The true raw-order Haar
statement has the form

```text
Phi_* ((rawHaar restricted to detChart).withDensity J)
  = rawHaar restricted to rawSourceChart.
```

For passive theta, without an additional endpoint pushforward comparison, the
safe local statement is bounded-density or scalar domination after supplying
the relevant hypothesis.  Do not assert

```text
Y_* referenceSource = rawHaar restricted to detChart
```

or exact raw-Haar transport for `rawMap_* referenceSource`.

There is a stronger obstruction to the unrestricted full-Haar target in the
nondegenerate Case 2 geometry.  The retained-passive `TopologyTuple` contains a
full family of `C` matrices, while `Case2PassiveTheta` supplies only
selected-entry center coordinates and fills the `C` family through the
Case 2 free-following residual constructor.  Hence the endpoint image is a
selected-entry chart-image slice inside the determinant chart, not an open
full-dimensional determinant-chart region.  The selected-entry weighted-box
change of variables gives Lebesgue measure on that selected-entry chart image,
not full retained-passive determinant-chart Haar.

## Kill Conditions

- Do not use bare `volume` on the nested passive-field product unless its
  measurable-space instance is proved to match the one used here.
- Do not assert exact Haar transport for `Y_*`.
- Do not target unrestricted full determinant-chart Haar for this theta
  domain unless the source is enlarged to include the missing full `C`
  coordinates.
- Do not drop the `Ctop` and `A1passive` unit hypotheses for determinant
  support.
- Do not use selected-entry inverse readout without the punctured condition
  `yNext(pivotNext) != 0`.
- Do not claim original source-prior transport, source-image coverage,
  source-rank coverage, normal crossings, pole order, or RLCT extraction from
  this reference-measure support layer.
