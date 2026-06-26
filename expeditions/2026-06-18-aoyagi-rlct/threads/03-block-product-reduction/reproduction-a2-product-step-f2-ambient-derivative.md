# Reproduction - A2 product-step F2 ambient derivative

Date: 2026-06-26.

Status: pen-and-paper check and Lean analytic derivative checkpoint for the
first inverse-dependent component of the p. 13 product-step coordinate change.

## Question

For the ambient tuple coordinate map

```text
(C1,D,F3old,A1,A2,A3,A4)
  -> (Ctop,D,A1,A3,F2,F3,C),
```

the `F2` coordinate is

```text
F2 = - A1^{-1} A2.
```

We want the Frechet derivative of this component at a determinant-chart point
`x`, and we want it to match the already-landed formal Jacobian component
`productReductionStepFormalJacobian_dF2 x`.

## Pen-and-Paper Check

Let the tangent vector be

```text
(dC1,dD,dF3old,dA1,dA2,dA3,dA4).
```

Only `A1` and `A2` enter `F2`.  The inverse derivative on the determinant
chart is

```text
d(A1^{-1})[dA1] = - A1^{-1} dA1 A1^{-1}.
```

Apply the product rule to `F2 = - A1^{-1} A2`:

```text
dF2
  = - ( d(A1^{-1})[dA1] A2 + A1^{-1} dA2 )
  = - ( - A1^{-1} dA1 A1^{-1} A2 + A1^{-1} dA2 )
  =   A1^{-1} dA1 A1^{-1} A2 - A1^{-1} dA2.
```

The formal Lean component is

```text
productReductionStepFormalJacobian_dF2 x
```

which expands to

```text
d ↦ A1^{-1} dA1 A1^{-1} A2 - A1^{-1} dA2.
```

This exactly matches the analytic first variation above.

## Lean Target

The component theorem has landed:

```text
hasFDerivAt_productReductionStepTopologyTupleToChart_F2
```

under `hA1 : IsUnit x.A1.det`, plus the finite-dimensional hypotheses needed
to coerce the formal linear map to a continuous linear map.

The Lean module also adds the reusable heterogeneous multiplication helper

```text
matrixMulContinuousLinearMap
matrixMulContinuousLinearMap_apply
```

for future `F3` and `C` derivative components.

## Guardrails

This component proves only one analytic coordinate derivative.  It does not
prove the full tuple derivative, determinant of the analytic derivative,
source-measure pushforward, density transport, change of variables for
integrals, normal crossings, pole order, or RLCT.
