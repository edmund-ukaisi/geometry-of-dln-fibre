# Reproduction - A2 Retained-Passive Solved A1 Zero Frechet Derivative

Date: 2026-06-27.

Status: pen-and-paper reproduction for the zero branch of the solved top-left
derivative.

## Setup

For a retained-passive tuple `z`, define

```text
Tfun(y) = retainedPassiveA1TailAfterFirst (ofTopologyTuple y).A1seed,
Tail    = Tfun(z),
dTail   = d(Tfun)_z(v).
```

The solved first top-left block is

```text
solvedA1(0)(y) = Tfun(y)^-1 * Ctop(y).
```

The determinant-chart hypothesis is used only to make `Tail` invertible for
the matrix-inverse derivative.

## Calculation

The product rule gives

```text
d_z(solvedA1(0))(v)
  = Tail^-1 * dCtop_z(v) + d_z(Tfun^-1)(v) * Ctop(z).
```

The endpoint top-left coordinate is a raw coordinate projection, hence

```text
dCtop_z(v) = v.2.2.2.2.1.
```

The matrix inverse derivative gives

```text
d_z(Tfun^-1)(v) = -(Tail^-1 * dTail * Tail^-1).
```

Substituting and preserving matrix multiplication order gives

```text
d_z(solvedA1(0))(v)
  = Tail^-1 * v.2.2.2.2.1
    - Tail^-1 * dTail * Tail^-1 * Ctop(z).
```

The middle `dTail` cannot be moved across either inverse-tail factor.

## Kill Conditions

- Do not remove the determinant-chart hypothesis.
- Do not rewrite this as a passive source tangent.
- Do not expand `dTail` into a recursive product formula in this theorem.
- Do not commute the factors in `Tail^-1 * dTail * Tail^-1 * Ctop`.

## Nonclaims

This proves only the zero solved-`A1` derivative in terms of the actual tail
Frechet derivative.  It does not prove a closed formula for `dTail`, does not
complete `dPcast` source-staging, and does not prove a determinant theorem,
measure theorem, normal-crossing theorem, pole order, or RLCT statement.
