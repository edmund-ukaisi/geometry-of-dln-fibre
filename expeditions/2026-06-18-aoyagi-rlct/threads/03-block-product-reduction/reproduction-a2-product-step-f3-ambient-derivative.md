# Reproduction - A2 product-step F3 ambient derivative

Date: 2026-06-26.

Status: landed.  Pen-and-paper check for the `F3` analytic component of the
p. 13 product-step coordinate change, formalised in Lean as
`hasFDerivAt_productReductionStepTopologyTupleToChart_F3`.

## Question

For the ambient tuple coordinate map

```text
(C1,D,F3old,A1,A2,A3,A4)
  -> (Ctop,D,A1,A3,F2,F3,C),
```

the `F3` coordinate is

```text
F3 = F3old - D A3 (C1 A1)^{-1}.
```

We want the Frechet derivative of this component at a determinant-chart point
`x`, and we want it to match `productReductionStepFormalJacobian_dF3 x`.

## Pen-and-Paper Check

Set

```text
Ctop  = C1 A1,
dCtop = dC1 A1 + C1 dA1.
```

The determinant-chart hypotheses are `det(C1)` and `det(A1)` units, so
`det(Ctop)` is a unit.  The inverse derivative gives

```text
d(Ctop^{-1}) = - Ctop^{-1} dCtop Ctop^{-1}.
```

For the triple product,

```text
d(D A3 Ctop^{-1})
  = dD A3 Ctop^{-1}
    + D dA3 Ctop^{-1}
    + D A3 d(Ctop^{-1})
  = dD A3 Ctop^{-1}
    + D dA3 Ctop^{-1}
    - D A3 Ctop^{-1} dCtop Ctop^{-1}.
```

Therefore

```text
dF3
  = dF3old
    - dD A3 Ctop^{-1}
    - D dA3 Ctop^{-1}
    + D A3 Ctop^{-1} dCtop Ctop^{-1}.
```

This is exactly the formal component

```text
productReductionStepFormalJacobian_dF3 x.
```

The sign of the final term is positive because it comes from subtracting the
inverse derivative contribution.

## Lean Target

The landed theorem is:

```text
hasFDerivAt_productReductionStepTopologyTupleToChart_F3
```

with hypotheses `IsUnit x.C1.det` and `IsUnit x.A1.det`.

Lean proves this by composing the landed `Ctop = C1*A1` derivative with the
matrix inverse derivative at `Ctop`, then applying the product rule to
`D*A3*Ctop^{-1}`.  The final equality against
`productReductionStepFormalJacobian_dF3` is checked by continuous-linear-map
extensionality and entrywise finite-sum normalization.

## Guardrails

This component proves only one analytic coordinate derivative.  It does not
prove the full tuple derivative, determinant of the analytic derivative,
source-measure pushforward, density transport, change of variables for
integrals, normal crossings, pole order, or RLCT.
