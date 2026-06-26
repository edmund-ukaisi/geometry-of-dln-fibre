# Reproduction - A2 product-step full ambient derivative

Date: 2026-06-26.

Status: landed.  Assembly of the component Frechet derivatives for the p. 13
product-step coordinate change, formalised in Lean as
`hasFDerivAt_productReductionStepTopologyTupleToChart`.

## Question

The ambient tuple map is

```text
(C1,D,F3old,A1,A2,A3,A4)
  -> (Ctop,D,A1,A3,F2,F3,C),
```

with

```text
Ctop = C1 A1
F2   = - A1^{-1} A2
F3   = F3old - D A3 (C1 A1)^{-1}
C    = A4 - A3 A1^{-1} A2.
```

The component derivatives have already been checked and landed:

```text
dCtop = dC1 A1 + C1 dA1
dF2   = A1^{-1} dA1 A1^{-1} A2 - A1^{-1} dA2
dF3   = dF3old
         - dD A3 Ctop^{-1}
         - D dA3 Ctop^{-1}
         + D A3 Ctop^{-1} dCtop Ctop^{-1}
dC    = dA4
         - dA3 A1^{-1} A2
         + A3 A1^{-1} dA1 A1^{-1} A2
         - A3 A1^{-1} dA2.
```

The remaining chart components are passive:

```text
dD = dD,    dA1 = dA1,    dA3 = dA3.
```

## Assembly Check

The chart tangent order is

```text
(dCtop,dD,dA1,dA3,dF2,dF3,dC).
```

Therefore the full derivative is the nested product of the landed component
derivatives in that order.  This is exactly the bundled formal p. 13 Jacobian

```text
productReductionStepFormalJacobian x.
```

The determinant-chart hypotheses needed for the full ambient derivative are

```text
IsUnit x.C1.det
IsUnit x.A1.det.
```

The `C1` hypothesis is used only through the `F3` component, to make
`Ctop = C1*A1` invertible.  The `A1` hypothesis is used by `F2`, `F3`, and
`C`.

## Lean Target

The landed theorem is:

```text
hasFDerivAt_productReductionStepTopologyTupleToChart
```

It states that `productReductionStepTopologyTupleToChart` has Frechet
derivative

```text
LinearMap.toContinuousLinearMap (productReductionStepFormalJacobian x)
```

at `x.topologyTuple`.

Lean proves this by applying `HasFDerivAt.prodMk` recursively to the component
theorems and the passive projection derivatives.

## Guardrails

This proves the full ambient Frechet derivative of the local coordinate
formula.  It does not prove analytic determinant unitness for this derivative,
source-measure pushforward, density transport, change of variables for
integrals, normal crossings, pole order, or RLCT.
