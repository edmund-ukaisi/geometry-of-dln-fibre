# Reproduction - A2 product-step determinant-chart image

Date: 2026-06-26.

Status: landed. Lean names:

```text
ProductReductionStepRawCoordinates.topologyTuple_mem_rawDetChartSet
productReductionStepRawCoordinatesOfTopologyTuple_of_topologyTuple
productReductionStepChartCoordinatesOfRawOrderTopologyTuple
productReductionStepChartCoordinatesOfRawOrderTopologyTuple_detChart
productReductionStepChartCoordinatesOfRawOrderTopologyTuple_rawOrder
ProductReductionStepChartCoordinates.rawOrderTopologyTuple_mem_rawDetChartSet
mapsTo_productReductionStepTopologyTupleToChartRawOrder_detChart
surjOn_productReductionStepTopologyTupleToChartRawOrder_detChart
bijOn_productReductionStepTopologyTupleToChartRawOrder_detChart
image_productReductionStepTopologyTupleToChartRawOrder_detChart
map_productReductionStepRawOrder_restrict_detChart_withDensity_absDet_eq_restrict_detChart
```

## Question

The previous weighted Haar theorem targets the image of the raw determinant
chart.  The next elementary bridge is to identify that image with the
raw-shaped target determinant chart.

## Pen-and-Paper Check

Write the raw tuple as

```text
(C1, D, F3_old, A1, A2, A3, A4)
```

with `det C1` and `det A1` nonzero.  The raw-order p. 13 map sends it to

```text
(Ctop, D, F3, A1, F2, A3, C)
```

where

```text
Ctop = C1 A1
F3   = F3_old - D A3 (C1 A1)^(-1)
F2   = -A1^(-1) A2
C    = A4 - A3 A1^(-1) A2.
```

The forward determinant chart condition is preserved because

```text
det Ctop = det(C1 A1) = det(C1) det(A1),
```

and the target `A1` coordinate is unchanged.

Conversely, a raw-shaped target tuple

```text
(Ctop, D, F3, A1, F2, A3, C)
```

with `det Ctop` and `det A1` nonzero is read as the chart record

```text
y = (Ctop, D, A1, A3, F2, F3, C).
```

The inverse formulas are

```text
C1     = Ctop A1^(-1)
D      = D
F3_old = F3 + D A3 Ctop^(-1)
A1     = A1
A2     = -A1 F2
A3     = A3
A4     = C - A3 F2.
```

The inverse determinant chart condition holds because

```text
det(Ctop A1^(-1)) = det(Ctop) det(A1^(-1)).
```

The record-level round-trip theorem
`productReductionStepCoordinate_right_inverse` then says this inverse maps
back to the original chart record; reordering the chart tuple into raw order
recovers the original raw-shaped target tuple. Thus the image of the raw
determinant chart is exactly the raw-shaped determinant chart.

## Guardrails

The target determinant chart is represented by the same tuple predicate
`productReductionStepRawDetChartSet`, but it is being read in raw-shaped target
order `(Ctop,D,F3,A1,F2,A3,C)`.  This is an image-identification statement for
the p. 13 coordinate map. It is not original DLN source/prior transport, not
source coverage, not a normal-crossing certificate, and not an RLCT or
pole-order theorem.

The strengthened Haar theorem rewrites the previous target `Phi '' S` to `S`
using this image equality. It remains weighted additive-Haar transport, not an
unweighted pushforward and not a statement about the original source measure.
