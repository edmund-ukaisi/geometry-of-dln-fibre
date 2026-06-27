# Reproduction - A2 retained-passive formal F2 recovery

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean proved; xhigh review
pending.

This note records the first determinant-relevant recovery brick for a future
staged target-side shear.  It is independent of the quiver-based paper.

## Setup

Fix an edge `p : Fin (M+1)` and abbreviate

```text
A = coord.solvedA1 p,
F = coord.F2 p.succ,
G = coord.solvedA3 p,
x = v.F2_p,
y = v.C_p.
```

For the formal raw-order map `u = retainedPassiveFormalRawOrderJacobianAt z v`,
the relevant two components are

```text
u.F2_p = -(A + F G) x + F y,
u.C_p  = -G x + y.
```

## Calculation

Compute in the target coordinates:

```text
F * u.C_p - u.F2_p
  = F * (-G x + y) - (-(A + F G) x + F y)
  = -F G x + F y + A x + F G x - F y
  = A x.
```

On the retained-passive determinant chart, `A.det` is a unit, so matrix inverse
cancellation gives

```text
A^{-1} * (F * u.C_p - u.F2_p) = x.
```

In Lean tuple notation:

```text
(coord.solvedA1 p)^-1 *
  (coord.F2 p.succ * u.2.2.2.1 p - u.2.1 p)
= v.2.1 p.
```

## Lean Target

```text
retainedPassiveFormalRawOrderJacobianAt_recovers_F2
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

The proof uses only `retainedPassiveFormalRawOrderJacobian_apply`, elementary
matrix algebra, `solvedA1_det_isUnit_of_detChart`, and
`Matrix.nonsing_inv_mul_cancel_left`.

## Guardrails

- This is a recovery identity for the formal map, not a statement about the
  actual Frechet derivative.
- It does not claim determinant equality by itself.
- The inverse `A^{-1}` occurs only in the off-diagonal target-coordinate
  recovery calculation; it is not inserted into the determinant-bearing formal
  map.
- The intended next determinant-relevant step is to use this recovery to build
  a staged target-side shear with determinant one.
