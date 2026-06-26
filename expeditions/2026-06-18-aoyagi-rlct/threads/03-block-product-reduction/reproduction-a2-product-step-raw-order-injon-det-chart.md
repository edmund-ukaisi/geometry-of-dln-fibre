# Reproduction - A2 product-step raw-order injectivity on determinant chart

Date: 2026-06-26.

Status: landed. Lean names:

```text
ProductReductionStepRawCoordinates.topologyTuple_injective
ProductReductionStepChartCoordinates.topologyTuple_injective
productReductionStepRawCoordinatesOfTopologyTuple
productReductionStepTopologyTupleToChart_ofTopologyTuple
injOn_productReductionStepTopologyTupleToChart_rawOrder_detChart
```

## Question

Mathlib's finite-dimensional Jacobian change-of-variables theorem needs
injectivity on the source set. For the p. 13 raw-order product-step map, the
source set is the raw determinant chart:

```text
S = {z | IsUnit z.1.det and IsUnit z.2.2.2.1.det}.
```

We need to prove that the raw-order tuple map is injective on `S`.

## Pen-and-Paper Check

Package each raw tuple `z` as a raw coordinate record

```text
X = (C1,D,F3old,A1,A2,A3,A4).
```

The condition `z in S` is exactly `X.detChart`, i.e. `det C1` and `det A1`
are units.

Suppose two raw tuples `z,w in S` have the same raw-order chart image. The
raw-order map is the chart-order tuple map followed by a linear coordinate
permutation. Since that permutation is an equivalence, equality of raw-order
images gives equality of chart-order tuple images.

The tuple map `ProductReductionStepChartCoordinates.topologyTuple` is
injective, so

```text
X.toChart = Y.toChart.
```

On the determinant chart, the landed inverse theorem gives

```text
(X.toChart).toRaw = X
(Y.toChart).toRaw = Y.
```

Applying `toRaw` to `X.toChart = Y.toChart` therefore gives `X = Y`. Finally,
the raw tuple map `ProductReductionStepRawCoordinates.topologyTuple` is
injective, so the original tuples are equal.

## Guardrails

This proves injectivity only on the raw determinant-chart set. It does not
prove a measure pushforward theorem, density transport, image identification
with the whole target determinant chart, source-stratum coverage, normal
crossings, pole order, or RLCT.

