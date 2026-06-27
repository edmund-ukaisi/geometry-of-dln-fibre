# Reproduction - A2 retained-passive formal C recovery

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; xhigh review PASS; Lean proved.

This is the companion recovery brick to the formal `F2` recovery.  It is
independent of the quiver-based paper.

## Setup

Fix an edge `p : Fin (M+1)` and abbreviate

```text
A = coord.solvedA1 p,
F = coord.F2 p.succ,
G = coord.solvedA3 p,
x = v.F2_p,
y = v.C_p.
```

For `u = retainedPassiveFormalRawOrderJacobianAt z v`, the formal edge pair is

```text
u.F2_p = -(A + F G) x + F y,
u.C_p  = -G x + y.
```

The previous brick recovers

```text
x = A^{-1} * (F * u.C_p - u.F2_p).
```

## Calculation

Substitute the recovered `x` into the `C` component:

```text
u.C_p + G * x
  = (-G x + y) + G x
  = y.
```

Equivalently, in target-coordinate-only form:

```text
u.C_p + G * (A^{-1} * (F * u.C_p - u.F2_p))
  = v.C_p.
```

The only invertibility used is the same determinant-chart invertibility of
`A` needed to recover `x`.

## Lean Target

```text
retainedPassiveFormalRawOrderJacobianAt_recovers_C
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Intended statement:

```text
let u := retainedPassiveFormalRawOrderJacobianAt z v
let coord := (ofTopologyTuple z).toCoordinateData
u.C_p
  + coord.solvedA3 p *
      ((coord.solvedA1 p)^-1 *
        (coord.F2 p.succ * u.C_p - u.F2_p))
= v.C_p.
```

## Guardrails

- This is a formal-map recovery identity, not an actual derivative theorem.
- It is not a determinant theorem by itself.
- It should use the previous formal `F2` recovery, not duplicate a larger
  determinant argument.
- The target-side shear factorization still remains to be built as a
  `LinearMap`/`LinearEquiv` statement.

## Independent Check

`Huygens the 5th`, xhigh read-only reviewer, returned PASS.  The reviewer
confirmed the noncommutative matrix order, use of the previous formal `F2`
recovery, absence of new determinant-chart requirements, and nonclaim boundary.
