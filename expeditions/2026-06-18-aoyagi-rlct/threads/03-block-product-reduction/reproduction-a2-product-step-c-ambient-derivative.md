# Reproduction - A2 product-step C ambient derivative

Date: 2026-06-26.

Status: landed.  Pen-and-paper check for the `C` analytic component of the
p. 13 product-step coordinate change, formalised in Lean as
`hasFDerivAt_productReductionStepTopologyTupleToChart_C`.

## Question

For the ambient tuple coordinate map

```text
(C1,D,F3old,A1,A2,A3,A4)
  -> (Ctop,D,A1,A3,F2,F3,C),
```

the `C` coordinate is

```text
C = A4 - A3 A1^{-1} A2.
```

We want the Frechet derivative of this component at a determinant-chart point
`x`, and we want it to match `productReductionStepFormalJacobian_dC x`.

## Pen-and-Paper Check

Set

```text
L = A3 A1^{-1}.
```

The determinant-chart hypothesis for this component is `det(A1)` a unit.  The
inverse derivative gives

```text
d(A1^{-1}) = - A1^{-1} dA1 A1^{-1}.
```

Differentiate the tail as `(A3 A1^{-1}) A2`:

```text
d(A3 A1^{-1})
  = dA3 A1^{-1} - A3 A1^{-1} dA1 A1^{-1}
  = dA3 A1^{-1} - L dA1 A1^{-1}.
```

Therefore

```text
d(A3 A1^{-1} A2)
  = dA3 A1^{-1} A2
    - L dA1 A1^{-1} A2
    + L dA2.
```

Since `C = A4 - A3 A1^{-1} A2`,

```text
dC
  = dA4
    - dA3 A1^{-1} A2
    + L dA1 A1^{-1} A2
    - L dA2.
```

This is exactly the formal component

```text
productReductionStepFormalJacobian_dC x.
```

The sign of the `dA1` term is positive because it comes from subtracting the
negative inverse-derivative contribution.

## Lean Target

The landed theorem is:

```text
hasFDerivAt_productReductionStepTopologyTupleToChart_C
```

with hypothesis `IsUnit x.A1.det`.

Lean proves this by differentiating `A3*A1^{-1}` first, then differentiating
`(A3*A1^{-1})*A2`.  This grouping matches the formal definition of
`productReductionStepFormalJacobian_dC`, so the final equality only needs
matrix associativity and entrywise simplification.

## Guardrails

This component proves only one analytic coordinate derivative.  It does not
prove the full tuple derivative, determinant of the analytic derivative,
source-measure pushforward, density transport, change of variables for
integrals, normal crossings, pole order, or RLCT.
