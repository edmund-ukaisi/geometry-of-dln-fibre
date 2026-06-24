# Statement Card - A2 one-step determinant-chart coordinate equivalence

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`

## Lean Names

```text
continuous_matrix_inv_of_forall_isUnit_det
ProductReductionStepRawCoordinates.instTopologicalSpace
ProductReductionStepChartCoordinates.instTopologicalSpace
ProductReductionStepRawCoordinates.continuous_toChart_detChart_subtype
ProductReductionStepRawCoordinates.continuous_detChart_toChart
ProductReductionStepChartCoordinates.continuous_toRaw_detChart_subtype
ProductReductionStepChartCoordinates.continuous_detChart_toRaw
productReductionStepCoordinate_detChart_homeomorph
```

Existing algebraic inputs:

```text
ProductReductionStepRawCoordinates.detChart_toChart
ProductReductionStepChartCoordinates.detChart_toRaw
productReductionStepCoordinate_left_inverse
productReductionStepCoordinate_right_inverse
```

## Statement Shape

For finite matrix index types over a nontrivially normed field, the one-step
p. 13 coordinate change

```text
(C1, D, F3_old, A1, A2, A3, A4)
  |-> (C1 A1, D, A1, A3, -A1^{-1}A2,
       F3_old - D A3 (C1 A1)^{-1},
       A4 - A3 A1^{-1} A2)
```

is a homeomorphism between the determinant-chart subtypes

```text
IsUnit det(C1) and IsUnit det(A1)
```

and

```text
IsUnit det(Ctop) and IsUnit det(A1).
```

The inverse is

```text
(Ctop, D, A1, A3, F2, F3, C)
  |-> (Ctop A1^{-1}, D, F3 + D A3 Ctop^{-1},
       A1, -A1 F2, A3, C - A3 F2).
```

## Scope

Finite determinant-chart topology and algebra for one product-reduction step.
The theorem identifies the chart variables as honest continuous local
coordinates on this finite determinant chart.

## Nonclaims

No analytic regularity, no analytic Jacobian determinant calculation, no
source-rank openness, no source coverage, no ideal-germ transport, no
regular-suspension certificate, no normal crossings, no pole-order theorem,
and no RLCT extraction.
