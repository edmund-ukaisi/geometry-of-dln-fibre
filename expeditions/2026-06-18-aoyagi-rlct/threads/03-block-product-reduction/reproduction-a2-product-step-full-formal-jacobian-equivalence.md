# Reproduction - A2 product-step full formal Jacobian equivalence

Date: 2026-06-26.

Status: pen-and-paper inverse-composition check and Lean equivalence
checkpoint for the full p. 13 one-step formal tangent formulas.

## Question

The previous checkpoint bundled the full p. 13 forward and inverse formal
tangent formulas as `LinearMap`s.  The next finite calculation is to check
that, at the chart base point induced by a raw base point, the inverse formula
and forward formula compose to the identity in both directions.

Let

```text
Q = C1*A1,
F2 = -(A1^-1*A2).
```

The raw-derived chart base point is

```text
(Q,D,A1,A3,F2,F3old - D*A3*Q^-1,A4 - A3*A1^-1*A2).
```

## Inverse After Forward

For raw tangent

```text
(dC1,dD,dF3old,dA1,dA2,dA3,dA4),
```

the inverse formula applied to the forward formula gives the raw tangent back.
The non-definitional components reduce as follows.

For `dC1`:

```text
((dC1*A1 + C1*dA1)*A1^-1)
  - (Q*A1^-1)*dA1*A1^-1
= dC1.
```

Use `(dC1*A1)*A1^-1 = dC1` and `Q*A1^-1 = C1`.

For old `dF3`:

```text
(dF3old - dD*A3*Q^-1 - D*dA3*Q^-1
  + D*A3*Q^-1*dCtop*Q^-1)
+ dD*A3*Q^-1 + D*dA3*Q^-1
- D*A3*Q^-1*dCtop*Q^-1
= dF3old.
```

This is pure additive cancellation.

For `dA2`:

```text
-dA1*(-A1^-1*A2)
  - A1*(A1^-1*dA1*A1^-1*A2 - A1^-1*dA2)
= dA2.
```

Use `-dA1*(-M)=dA1*M` and `A1*(A1^-1*N)=N`.

For `dA4`:

```text
(dA4 - dA3*A1^-1*A2 + A3*A1^-1*dA1*A1^-1*A2
  - A3*A1^-1*dA2)
- dA3*(-A1^-1*A2)
- A3*(A1^-1*dA1*A1^-1*A2 - A1^-1*dA2)
= dA4.
```

Use `dA3*(-M)=-(dA3*M)`, distribute the final `A3*`, and cancel
additively.

## Forward After Inverse

For chart tangent

```text
(eQ,eD,eA1,eA3,eF2,eF3,eC),
```

first recover the `dCtop` component:

```text
(eQ*A1^-1 - Q*A1^-1*eA1*A1^-1)*A1 + C1*eA1
= eQ.
```

Again the only multiplicative cancellations are `A1^-1*A1=1` and
`Q*A1^-1=C1`.

The `dF3` component then becomes

```text
eF3 + eD*A3*Q^-1 + D*eA3*Q^-1 - D*A3*Q^-1*eQ*Q^-1
- eD*A3*Q^-1 - D*eA3*Q^-1 + D*A3*Q^-1*eQ*Q^-1
= eF3.
```

For `dF2`:

```text
A1^-1*eA1*A1^-1*A2
  - A1^-1*(-eA1*(-A1^-1*A2) - A1*eF2)
= eF2.
```

For `dC`:

```text
(eC - eA3*(-A1^-1*A2) - A3*eF2)
- eA3*A1^-1*A2
+ A3*A1^-1*eA1*A1^-1*A2
- A3*A1^-1*(-eA1*(-A1^-1*A2) - A1*eF2)
= eC.
```

Both are the same sign/distribution calculation as above.

## Lean Target Landed

`ProductReductionStepJacobian.lean` now proves the formula-composition
identities

```text
productReductionStepFormalJacobianInverseFormula_formula_chartBase
productReductionStepFormalJacobianFormula_inverseFormula_chartBase
```

and bundles the full p. 13 raw/chart formal tangent map as

```text
productReductionStepFormalJacobianEquiv
productReductionStepFormalJacobianEquiv_apply
productReductionStepFormalJacobianEquiv_symm_apply
```

## Guardrails

This checkpoint proves a finite raw/chart `LinearEquiv`.  It does not yet
state a determinant-unit theorem for the full Jacobian.  The native codomain is
chart ordered, so a determinant statement should first compose with
`productReductionStepChartTangentRawOrderEquiv`.

It also does not prove analytic differentiability, source-measure pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT.
