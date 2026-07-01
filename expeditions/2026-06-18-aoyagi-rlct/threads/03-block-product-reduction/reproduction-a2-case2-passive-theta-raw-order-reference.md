# Reproduction - A2 Case 2 passive-theta raw-order reference

Date: 2026-07-01.

Status: pen-and-paper reproduction for the raw-order image of the concrete
passive-theta reference source.

## Question

After naming the endpoint image measure

```text
Y_* (referenceSource restricted to V),
```

what is the honest next image-measure target after applying the retained
passive raw-order map

```text
Phi = topologyTupleEdgeRawOrder?
```

The target must avoid the false claim that the endpoint image is unrestricted
determinant-chart Haar.

## Local Maps

Fix a Case 2 passive-theta coordinate

```text
theta = (A1passive, F2, A3passive, Ctop, F3, yNext).
```

The endpoint topology tuple is

```text
Y(theta) =
  case2PassiveThetaEndpointTopologyTuple ... theta eNext e.
```

On the determinant chart, the retained-passive raw-order map is

```text
Phi =
  topologyTupleEdgeRawOrder.
```

The raw-order passive-theta map is therefore

```text
rawMap(theta) = Phi(Y(theta)).
```

This map is used only after shrinking to a local determinant/punctured sector.
The existing local theorem supplies an open set `V` such that, for every
`theta in V`,

```text
Y(theta) in topologyTupleDetChartSet,
rawMap(theta) in topologyTupleRawOrderSourceRecursiveDetChartSet,
rawChart(rawMap(theta)) = sourceChart(theta).
```

The punctured condition `yNext(pivotNext) != 0` enters through this local
source-chart/raw-order package.  It is not needed for determinant support
alone, but it is needed for the inverse readout and raw-chart equality.

## Reference Image

The concrete theta reference source is

```text
referenceSource =
  case2PassiveThetaReferenceSourceMeasure
    = passiveFieldReference.prod centerWeightedBox.
```

The raw-order reference image measure is the actual image measure

```text
case2PassiveThetaRawOrderReferenceImageMeasure ... V
  = Measure.map rawMap (referenceSource.restrict V).
```

This is a named image measure, not raw Haar.

## Support Calculation

On the local set `V`, every `theta` satisfies

```text
rawMap(theta) in rawSourceSet,
rawSourceSet = topologyTupleRawOrderSourceRecursiveDetChartSet.
```

The raw map is a.e. measurable for any measure restricted to `V`: on `V`,
`Y(theta)` is in the determinant chart, `Y` is continuous, and
`Phi` is continuous on the determinant-chart subtype.  Hence `rawMap` is
continuous on `V`, and therefore a.e. measurable after restricting to `V`.

Applying the usual image-support lemma gives

```text
(Measure.map rawMap (referenceSource.restrict V)).restrict rawSourceSet
  =
Measure.map rawMap (referenceSource.restrict V).
```

Equivalently,

```text
(case2PassiveThetaRawOrderReferenceImageMeasure ... V).restrict rawSourceSet
  =
case2PassiveThetaRawOrderReferenceImageMeasure ... V.
```

## Domination Calculation

Suppose a passive-field measure is dominated by the concrete passive-field
reference:

```text
passiveMeasure <= d • passiveFieldReference.
```

Taking product with the same center weighted box gives

```text
passiveMeasure.prod weightedBox
  <= d • passiveFieldReference.prod weightedBox.
```

Restricting to `V` preserves domination, and pushing forward by the locally
a.e. measurable `rawMap` preserves the scalar domination:

```text
Measure.map rawMap ((passiveMeasure.prod weightedBox).restrict V)
  <=
d • Measure.map rawMap (referenceSource.restrict V).
```

The right-hand side is exactly

```text
d • case2PassiveThetaRawOrderReferenceImageMeasure ... V.
```

## Boundary

This statement deliberately stops at the raw-order image measure.  It does not
identify the image with unrestricted raw Haar, determinant-chart Haar, or a
full-dimensional coordinate-volume measure.

The obstruction remains the same as at the endpoint level: the passive-theta
domain contains selected-entry residual center coordinates, while the retained
passive topology tuple has a full `C` family.  The image is a chart-image
slice, not the whole raw-order determinant chart.

## Kill Conditions

- Do not replace the raw-order image measure by unrestricted raw Haar.
- Do not use the raw-order map outside the local determinant-chart support
  supplied by the existing punctured-sector theorem.
- Do not drop the nonzero pivot hypothesis when invoking the source-chart
  raw-order package.
- Do not claim a Jacobian or normal-crossing result here.
