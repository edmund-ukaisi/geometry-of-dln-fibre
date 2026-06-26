# Reproduction - A2 product-step full formal linear maps

Date: 2026-06-26.

Status: Lean packaging checkpoint for the full p. 13 one-step formal tangent
formulas. The source formulas are the ones reproduced in
`reproduction-a2-product-step-full-formal-jacobian-formulas.md`; this note
checks that they can be bundled as linear maps at a fixed base point.

## Fixed-Base Linearity

At a fixed raw base point

```text
x = (C1,D,F3old,A1,A2,A3,A4),
Q = C1*A1,
```

the forward formal tangent components are linear in the raw tangent variables:

```text
dCtop = dC1*A1 + C1*dA1
dD    = dD
dA1   = dA1
dA3   = dA3

dF2 = A1^-1*dA1*A1^-1*A2 - A1^-1*dA2

dF3 = dF3old
      - dD*A3*Q^-1
      - D*dA3*Q^-1
      + D*A3*Q^-1*dCtop*Q^-1

dC = dA4
     - dA3*A1^-1*A2
     + A3*A1^-1*dA1*A1^-1*A2
     - A3*A1^-1*dA2.
```

Each term is a fixed left/right matrix multiplication applied to one tangent
component, or a sum/difference of such terms. In Lean this is built from
`mulLeftLinearMap`, `mulRightLinearMap`, projections from the nested raw
tangent tuple, and `LinearMap.prod`.

At a fixed chart base point

```text
y = (Q,D,A1,A3,F2,F3,C),
```

the inverse formal tangent components are likewise linear:

```text
dC1    = eQ*A1^-1 - Q*A1^-1*eA1*A1^-1
dD     = eD
dF3old = eF3
         + eD*A3*Q^-1
         + D*eA3*Q^-1
         - D*A3*Q^-1*eQ*Q^-1
dA1    = eA1
dA2    = -eA1*F2 - A1*eF2
dA3    = eA3
dA4    = eC - eA3*F2 - A3*eF2.
```

No inverse of `D`, `A3`, or `C` appears.

## Lean Target Landed

`ProductReductionStepJacobian.lean` now defines bundled linear maps

```text
productReductionStepFormalJacobian
productReductionStepFormalJacobianInverse
```

and proves their pointwise equality with the already reviewed tuple formulas:

```text
productReductionStepFormalJacobian_apply
productReductionStepFormalJacobianInverse_apply
```

The construction also introduces named raw/chart tangent projections and
component maps for the nontrivial forward and inverse coordinates.

## Guardrails

This checkpoint does not prove that the forward and inverse bundled maps
compose to the identity. It therefore does not yet define the full raw/chart
`LinearEquiv`, the raw-order endomorphism, or the determinant-unit theorem.

It also does not prove analytic differentiability, source-measure pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT.
