# Reproduction - A2 retained-passive F3 positive-tail dLast target staging

Date: 2026-06-27.

Status: Lean proved; focused and full builds passed; independent xhigh
implementation review passed; sorry/whitespace/axiom audits passed.

This note is independent of the quiver-based paper.  It isolates only the
terminal top-factor derivative appearing in the retained-passive `F3` bridge
when `0 < M`.  It does not reproduce or target-stage the early lower-left tail
derivative.

## Setup

Work at a retained-passive raw tuple `z` in the determinant chart, with tangent
`v`.  Write

```text
raw    = topologyTupleEdgeRawOrder,
data   = ofTopologyTuple z,
coord  = data.toCoordinateData,
Dzv    = d(raw)_z(v),
formal = retainedPassiveFormalRawOrderJacobianAt(z)(v).
```

The landed `F3` bridge uses

```text
A1fun(y)(p) = coord_y.solvedA1(p),

Early(y) =
  retainedPassiveLowerLeftProductTailSum
    A1fun(y)
    (retainedPassiveA3WithoutLast A3seed(y))
    C(y)
    0,

Last(y) =
  residualFactorProduct A1fun(y)
    (Fin.last (M+1))
    (Fin.last M).castSucc.
```

It proves

```text
Dzv.F3
  - dEarly_z(v) * Last(z)
  + (coord.F3 - Early(z)) * dLast_z(v)
= formal.F3.
```

The order is part of the claim: `dEarly_z(v)` and `dLast_z(v)` multiply on the
right of the lower-left row block where displayed.

## Terminal top factor

Assume `0 < M`.  Choose a passive terminal index

```text
q : Fin M,     hq : q.succ = Fin.last M.
```

The terminal top residual product is a one-edge product.  The existing product
identity gives

```text
Last(y) = A1fun(y)(Fin.last M).
```

Using `hq`, this becomes

```text
Last(y) = A1fun(y)(q.succ).
```

Since `q.succ != 0`, the solved top-left family is passive at this slot:

```text
A1fun(y)(q.succ)
  = data_y.A1seed(q.succ)
  = data_y.A1passive(q)
  = y.A1passive(q).
```

Therefore

```text
dLast_z(v) = v.A1passive(q).
```

This calculation is elementary coordinate projection.  It uses no normal
crossing extraction, no determinant formula, and no lower-left early-tail
recurrence.

## Target-staged passive top derivative

The landed passive `A1` target-staged recovery theorem, applied at `q`, gives

```text
targetLast(q) =
  Dzv.A1passive(q)
    - XsuccF2(q.succ) * coord.solvedA3(q.succ)
    - coord.F2(q.succ.succ) * rawEdgeTupleA3(Dzv,q.succ)
= v.A1passive(q),
```

where

```text
XsuccF2 = retainedPassiveTargetRecoveredSuccessorF2At(z,Dzv).
```

Combining this with the terminal top derivative calculation gives

```text
dLast_z(v) = targetLast(q).
```

The term

```text
rawEdgeTupleA3(Dzv,q.succ)
```

is not asserted to be zero.  Because `q.succ = Fin.last M`, the displayed
correction is the terminal successor correction, and it is kept under its
explicit multiplier `coord.F2(q.succ.succ)`.

## Substitution into the F3 bridge

Only the `dLast` factor is replaced.  The early-tail value and derivative stay
as they appear in the landed bridge:

```text
Dzv.F3
  - dEarly_z(v) * LastTop
  + (coord.F3 - Early(z)) * targetLast(q)
= formal.F3,
```

where

```text
LastTop = coord.solvedA1(Fin.last M).
```

The recovery theorem then right-multiplies by the inverse of the negative
terminal solved top block:

```text
(staged_F3_expression) * (-(coord.solvedA1(Fin.last M)))^{-1} = v.F3.
```

## Boundary checks

- This is a `dLast` substitution only.  It does not target-stage `dEarly`.
- `Last` is the terminal solved top block, not the first passive tail.
- The raw terminal lower-left target readout is not set to zero.
- The determinant-chart hypothesis remains explicit through the consumed
  passive `A1` recovery theorem.

## Kill conditions

- If `Last` is confused with `retainedPassiveA1TailAfterFirst`, the slice is
  wrong.
- If the theorem removes or zeroes `rawEdgeTupleA3(Dzv,q.succ)`, it overclaims.
- If the theorem advertises positive-tail `F3` target staging while still
  leaving source tangents other than `dEarly`, the statement is misnamed.
- If the result is read as a determinant-one target-side shear, determinant
  equality, measure transport, normal crossings, pole order, or RLCT, it
  overclaims.

## Nonclaims

No positive-tail full `F3` target staging, no derivative recurrence for
`Early`, no whole-tuple target-side normalization, no determinant-one
`LinearEquiv`, no actual derivative determinant formula, no measure transport,
no normal crossings, no pole order, and no RLCT follows from this slice.
