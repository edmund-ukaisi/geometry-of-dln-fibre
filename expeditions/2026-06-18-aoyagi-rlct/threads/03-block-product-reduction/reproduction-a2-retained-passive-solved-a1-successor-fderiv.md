# Reproduction - A2 Retained-Passive Solved A1 Successor Frechet Derivative

Date: 2026-06-27.

Status: pen-and-paper reproduction for the successor branch of the solved
top-left derivative.  This is independent of the inverse-tail zero branch.

## Setup

Work in retained-passive raw tuple coordinates

```text
z = (A1passive, F2, A3passive, C, Ctop, F3).
```

The full seed family is

```text
A1seed(0) = 0,
A1seed(p.succ) = A1passive(p).
```

The solved full top-left family is

```text
solvedA1(0)      = Tail(A1seed)^-1 * Ctop,
solvedA1(p.succ) = A1seed(p.succ).
```

The successor case uses only the second line.  It does not use the determinant
chart, the tail product, or matrix inversion.

## Calculation

Fix `p : Fin M`.  Since `p.succ != 0`, the definition of
`retainedPassiveSolvedA1` gives, for every tuple `y`,

```text
(ofTopologyTuple y).toCoordinateData.solvedA1(p.succ)
  = (ofTopologyTuple y).A1seed(p.succ)
  = y.1(p).
```

Therefore the map whose derivative is needed is exactly the coordinate
projection

```text
y |-> y.1(p).
```

Let `LA1_p` be the continuous linear map

```text
LA1_p(y) = y.1(p).
```

Then

```text
fderiv (fun y => y.1(p)) z = LA1_p,
```

so applying to a tangent tuple `v` gives

```text
d_z(solvedA1(p.succ))(v) = v.1(p).
```

## Kill Conditions

- Do not add a determinant-chart hypothesis to this successor formula.  The
  inverse-tail branch needs it; the successor branch does not.
- Do not rewrite the `p = 0` branch as a passive tangent.  The zero branch is
  `Tail^-1*dCtop - Tail^-1*dTail*Tail^-1*Ctop`.
- Do not import or depend on the downstream Jacobian/formal raw-order file.
  This formula is a derivative-file foothold.

## Nonclaims

This proves only the successor solved-`A1` derivative formula.  It does not
compute the derivative of `solvedA1(0)`, does not expand `dTail`, does not
source-stage `dPcast`, and does not prove a raw-order derivative determinant,
measure theorem, normal-crossing theorem, pole order, or RLCT statement.
