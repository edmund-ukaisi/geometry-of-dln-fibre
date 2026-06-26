# Reproduction - A2 product-step ambient derivative

Date: 2026-06-26.

Status: pen-and-paper derivative check and first Lean analytic derivative
checkpoint after the finite formal tangent calculation.

## Question

The previous checkpoints proved that the p. 13 product-step formal tangent
map is a linear equivalence and has determinant a unit.  The next analytic
step is to identify this formal tangent map with the Frechet derivative of the
actual coordinate formulas, at least on the ambient tuple space before passing
to determinant-chart subtypes.

The raw variables are

```text
(C1,D,F3old,A1,A2,A3,A4)
```

and the chart variables are

```text
(Ctop,D,A1,A3,F2,F3,C)
```

with

```text
Ctop = C1 A1
F2   = - A1^{-1} A2
F3   = F3old - D A3 (C1 A1)^{-1}
C    = A4 - A3 A1^{-1} A2.
```

The determinant-chart hypotheses are

```text
det(C1) is a unit,
det(A1) is a unit.
```

They imply that `Ctop = C1 A1` also has determinant a unit.

## Inverse Derivative

For an invertible square matrix `A`, differentiating

```text
(A + eps H)^{-1} (A + eps H) = I
```

at `eps = 0` gives

```text
d(A^{-1})[H] A + A^{-1} H = 0.
```

Multiplying on the right by `A^{-1}` yields

```text
d(A^{-1})[H] = - A^{-1} H A^{-1}.
```

This is the standard normed-ring inverse derivative.  In Lean the first
analytic checkpoint should therefore be a reusable real matrix theorem:

```text
HasFDerivAt (fun B => B^{-1})
  (fun H => - A^{-1} H A^{-1}) A
```

under `IsUnit A.det`.  This theorem is generic analytic infrastructure, not a
change-of-variables theorem.

## Product-Step First Variation

Let

```text
(dC1,dD,dF3old,dA1,dA2,dA3,dA4)
```

be a tangent vector and set

```text
Ctop  = C1 A1
dCtop = dC1 A1 + C1 dA1.
```

The product rule gives the passive chart components immediately:

```text
dD = dD,   dA1 = dA1,   dA3 = dA3.
```

For `F2 = - A1^{-1} A2`, the inverse derivative gives

```text
dF2 = -((-A1^{-1} dA1 A1^{-1}) A2 + A1^{-1} dA2)
     = A1^{-1} dA1 A1^{-1} A2 - A1^{-1} dA2.
```

For `F3 = F3old - D A3 Ctop^{-1}`, the product rule and
`d(Ctop^{-1}) = -Ctop^{-1} dCtop Ctop^{-1}` give

```text
dF3 =
  dF3old
  - dD A3 Ctop^{-1}
  - D dA3 Ctop^{-1}
  + D A3 Ctop^{-1} dCtop Ctop^{-1}.
```

For `C = A4 - A3 A1^{-1} A2`, the same calculation gives

```text
dC =
  dA4
  - dA3 A1^{-1} A2
  + A3 A1^{-1} dA1 A1^{-1} A2
  - A3 A1^{-1} dA2.
```

These are exactly the components already encoded by
`productReductionStepFormalJacobianFormula`.

## Lean Target Landed

The safe next Lean target is not a derivative theorem on the determinant-chart
subtype, because the subtype is not the ambient vector space expected by
`HasFDerivAt`.  The correct first analytic target is an ambient tuple theorem:

```text
HasFDerivAt productReductionStepToChartTuple
  (LinearMap.toContinuousLinearMap (productReductionStepFormalJacobian x))
  x.topologyTuple
```

where `productReductionStepToChartTuple` is the tuple-level version of
`ProductReductionStepRawCoordinates.toChart`.

Lean now lands the first part of this target in
`ProductReductionStepDerivative.lean`:

```text
hasFDerivAt_matrix_inv_of_isUnit_det
productReductionStepTopologyTupleToChart
productReductionStepTopologyTupleToChart_topologyTuple
productReductionStepTopologyTupleToChart_topologyTuple_chartBase
hasFDerivAt_productReductionStepTopologyTupleToChart_Ctop
```

The full tuple derivative remains open, but the module now has the correct
ambient map, the matrix-inverse derivative, and the exact `Ctop` component
identification with `productReductionStepFormalJacobian_dCtop`.

## Guardrails

This checkpoint only identifies the Frechet derivative of the local coordinate
formula in ambient finite-dimensional real matrix coordinates.  It does not
prove source-measure pushforward, density transport, determinant absolute
value, chart coverage, exact-rank source openness, normal crossings, pole
order, or RLCT.
