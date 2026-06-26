# Reproduction - A2 product-step raw-order ambient derivative

Date: 2026-06-26.

Status: landed.  Composition of the full ambient Frechet derivative with the
chart-output reorder equivalence, formalised in Lean as
`hasFDerivAt_productReductionStepTopologyTupleToChart_rawOrder`.

## Question

The full ambient derivative theorem lands the derivative in chart tangent
order:

```text
(dCtop,dD,dA1,dA3,dF2,dF3,dC).
```

The finite determinant-unit certificate was proved for the raw-shaped output
order:

```text
(dCtop,dD,dF3,dA1,dF2,dA3,dC).
```

The reorder is the linear equivalence

```text
productReductionStepChartTangentRawOrderEquiv.
```

We want the Frechet derivative of the composite

```text
z |-> productReductionStepChartTangentRawOrderEquiv
        (productReductionStepTopologyTupleToChart z)
```

to be the raw-order formal Jacobian

```text
productReductionStepFormalJacobianRawOrder x.
```

## Check

The landed full ambient derivative theorem gives

```text
D(productReductionStepTopologyTupleToChart)_x
  = productReductionStepFormalJacobian x.
```

The reorder equivalence is linear, so its derivative is itself.  The chain
rule gives

```text
D(reorder o productStep)_x
  = reorder o productReductionStepFormalJacobian x
  = productReductionStepFormalJacobianRawOrder x.
```

This is exactly the raw-shaped endomorphism whose determinant unitness was
already proved as

```text
productReductionStepFormalJacobianRawOrder_det_isUnit.
```

## Lean Target

The landed theorem is:

```text
hasFDerivAt_productReductionStepTopologyTupleToChart_rawOrder
```

with determinant-chart hypotheses `IsUnit x.C1.det` and `IsUnit x.A1.det`.

Lean proves it by composing the landed full ambient derivative theorem with
the continuous-linear map underlying
`productReductionStepChartTangentRawOrderEquiv`.

## Guardrails

This theorem identifies the raw-order derivative map and connects it to the
finite determinant-unit formal certificate.  It does not by itself prove a
subtype chart theorem, source-measure pushforward, density transport, change
of variables for integrals, normal crossings, pole order, or RLCT.
