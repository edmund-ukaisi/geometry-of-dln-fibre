# Reproduction - A2 product-step full formal Jacobian formulas

Date: 2026-06-26.

Status: pen-and-paper reproduction for the full p. 13 one-step formal tangent
formulas, plus the determinant-order bookkeeping needed for a future
determinant theorem.

## Question

The previous fixed-passive slice varied only `(C1,F3old,A2,A4)` and held
`D`, `A1`, and `A3` fixed.  The full p. 13 one-step coordinate change varies
all raw variables

```text
(C1,D,F3old,A1,A2,A3,A4).
```

The chart variables are ordered as

```text
(Ctop,D,A1,A3,F2,F3,C).
```

Because the raw and chart tuple orders differ, a determinant theorem cannot be
stated directly for the raw-to-chart map.  A future determinant theorem must
compose with a chart-output reorder equivalence.

## Coordinate Formulas

The one-step p. 13 formulas are

```text
Ctop = C1 * A1
F2   = -(A1^-1 * A2)
F3   = F3old - D * A3 * (C1 * A1)^-1
C    = A4 - A3 * A1^-1 * A2.
```

Set

```text
Q  = Ctop = C1 * A1
dQ = dC1 * A1 + C1 * dA1.
```

## Forward Formal Tangent Formula

Using

```text
d(A1^-1) = -A1^-1 * dA1 * A1^-1
d(Q^-1)  = -Q^-1 * dQ * Q^-1,
```

the raw tangent

```text
(dC1,dD,dF3old,dA1,dA2,dA3,dA4)
```

maps to chart-order tangent

```text
(dCtop,dD,dA1,dA3,dF2,dF3,dC)
```

by

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

The `dF3` inverse-variation term has positive sign; the `dD` and `dA3` terms
are negative.  The `dC` term from varying `A1^-1` has positive sign.

## Inverse Formal Tangent Formula

At chart base point `(Q,D,A1,A3,F2,F3,C)`, a chart tangent

```text
(eQ,eD,eA1,eA3,eF2,eF3,eC)
```

maps to raw order

```text
(dC1,dD,dF3old,dA1,dA2,dA3,dA4)
```

by

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

## Determinant-Order Bookkeeping

The raw tangent order is

```text
(C1,D,F3old,A1,A2,A3,A4).
```

The chart tangent order is

```text
(Ctop,D,A1,A3,F2,F3,C).
```

For determinant unitness, the chart output should first be reordered to the
raw-shaped order

```text
(Ctop,D,F3,A1,F2,A3,C).
```

This is a pure coordinate permutation and contributes only a unit determinant,
but it must be explicit in Lean.  Suppressing it would make the determinant
statement ill-typed or ambiguous.

## Lean Target Landed

`ProductReductionStepJacobian.lean` now records:

```text
ProductReductionStepRawTangent
ProductReductionStepChartTangent
productReductionStepFormalJacobianFormula
productReductionStepFormalJacobianInverseFormula
productReductionStepChartTangentRawOrderEquiv
```

The first two formula definitions are tuple-valued formulas, not yet bundled
as `LinearMap`s.  The final equivalence is the chart-output reorder needed by
a future determinant theorem.

## Guardrails

This slice does not prove:

- linearity of the full formula as a bundled `LinearMap`;
- inverse composition as a `LinearEquiv`;
- determinant unitness of the full Jacobian;
- analytic differentiability or `HasFDerivAt`;
- source-measure pushforward or density/Jacobian transport;
- normal crossings, pole order, or RLCT.
