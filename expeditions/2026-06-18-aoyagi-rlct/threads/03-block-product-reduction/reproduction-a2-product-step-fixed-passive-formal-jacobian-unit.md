# Reproduction - A2 product-step fixed-passive formal Jacobian unit

Date: 2026-06-26.

Status: pen-and-paper reproduction for a focused p. 13 formal tangent slice.

## Question

The Schur-core Jacobian slice fixed the pivot block `B` and varied only
`(A2,A3,A4)`. The next elementary p. 13 coordinate-change slice lets the top
block `C1` vary, but still fixes the passive parameters `D`, `A1`, and `A3`.

This is not the full p. 13 tangent map. The full tangent map also varies `D`,
`A1`, and `A3`, and therefore has extra `dD`, `dA1`, and `dA3` terms.

## Source Anchors

Aoyagi PDF pp. 11-13 performs one product-reduction step by changing from raw
blocks

```text
(C1, D, F3old, A1, A2, A3, A4)
```

to chart blocks

```text
(Ctop, D, A1, A3, F2, F3, C)
```

on the determinant chart. The local coordinate formulas already formalised in
`ProductReduction.lean` are

```text
Ctop = C1 * A1
F2   = -(A1^-1 * A2)
F3   = F3old - D * A3 * (C1 * A1)^-1
C    = A4 - A3 * A1^-1 * A2.
```

This reproduction treats `D`, `A1`, and `A3` as fixed parameters and computes
the formal linearisation in the variables `(C1,F3old,A2,A4)`.

## Forward Formal Differential

Set

```text
B  = C1 * A1
dB = dC1 * A1.
```

Using the formal inverse rule

```text
d(B^-1) = -B^-1 * dB * B^-1,
```

the fixed-passive differential of the forward coordinate change is

```text
dCtop = dC1 * A1

dF2   = -(A1^-1 * dA2)

dF3   = dF3old
        + D * A3 * B^-1 * dB * B^-1

dC    = dA4 - A3 * A1^-1 * dA2.
```

The sign in `dF3` is positive because the coordinate formula contains
`-D*A3*B^-1`; differentiating the inverse contributes the extra minus sign.

## Inverse Formal Differential

For chart tangent variables `(dCtop,dF3,dF2,dC)`, with `D`, `A1`, `A3`, and
`Ctop` fixed at the base chart point, the inverse coordinate formulas give

```text
dC1    = dCtop * A1^-1

dF3old = dF3
         - D * A3 * Ctop^-1 * dCtop * Ctop^-1

dA2    = -A1 * dF2

dA4    = dC - A3 * dF2.
```

## Composition Check

For raw-to-chart-to-raw, let

```text
U = D * A3 * B^-1 * (dC1 * A1) * B^-1.
```

Then the four components are

```text
(dC1 * A1) * A1^-1 = dC1,
(dF3old + U) - U = dF3old,
-A1 * (-(A1^-1 * dA2)) = dA2,
(dA4 - A3*A1^-1*dA2) - A3*(-A1^-1*dA2) = dA4.
```

Only the `A1` inverse cancellation is used.

For chart-to-raw-to-chart, the corresponding cancellations are

```text
(dCtop * A1^-1) * A1 = dCtop,
(dF3 - V) + V = dF3,
-(A1^-1 * (-A1 * dF2)) = dF2,
(dC - A3*dF2) - A3*A1^-1*(-A1*dF2) = dC,
```

where

```text
V = D * A3 * Ctop^-1 * dCtop * Ctop^-1.
```

Again no inverse of `D` is used. The determinant-chart hypothesis
`IsUnit C1.det` is source-faithful and implies `IsUnit (C1*A1).det` together
with `IsUnit A1.det`, but this fixed-passive inverse calculation only needs
the `A1` cancellations.

## Lean Target

The Lean slice in `ProductReductionStepJacobian.lean` introduces

```text
ProductStepFixedPassiveRawTangent
ProductStepFixedPassiveChartTangent
productStepFixedPassiveFormalJacobian
productStepFixedPassiveFormalJacobianInverse
productStepFixedPassiveFormalJacobianEquiv
productStepFixedPassiveFormalJacobian_det_isUnit
```

The determinant theorem is finite-dimensional: `rho` and `mu` are already
`Fintype`, and the theorem assumes `[Finite pi] [Finite nu]` before using
`LinearMap.det`.

## Guardrails

This slice does not prove:

- the full p. 13 formal Jacobian for varying `(C1,D,F3old,A1,A2,A3,A4)`;
- `HasFDerivAt` or analytic differentiability;
- source-measure pushforward or density/Jacobian transport;
- exact determinant exponent or sign;
- chart coverage, source/image equality, normal crossings, pole order, or
  RLCT extraction.
