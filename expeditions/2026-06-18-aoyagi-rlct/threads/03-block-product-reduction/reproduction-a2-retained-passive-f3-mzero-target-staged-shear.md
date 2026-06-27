# Reproduction - A2 retained-passive F3 zero-tail target-staged shear

Date: 2026-06-27.

Status: Lean proved; focused and full builds passed; sorry/whitespace/axiom
audits passed; independent xhigh checker passed.

This note is independent of the quiver-based paper.  It isolates the
single-edge retained-passive `F3` component (`M = 0`) after the landed Ctop
target-staged endpoint shear.  It is not a full positive-tail `F3` target
staging theorem.

## Setup

Work at a retained-passive raw tuple `z` in the determinant chart, with tangent
`v`.  Write

```text
raw    = topologyTupleEdgeRawOrder,
coord  = (ofTopologyTuple z).toCoordinateData,
Dzv    = d(raw)_z(v),
formal = retainedPassiveFormalRawOrderJacobianAt(z)(v).
```

The landed `F3` component bridge uses

```text
Early(y) =
  retainedPassiveLowerLeftProductTailSum
    solvedA1(y)
    (retainedPassiveA3WithoutLast A3seed(y))
    C(y)
    0,

Last(y) =
  residualFactorProduct solvedA1(y)
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

The order is part of the claim: all correction factors multiply on the right.
This formula comes from differentiating

```text
raw.F3 = -(coord.F3 - Early) * Last.
```

## The zero-tail collapse

Now assume `M = 0`.  There is one retained edge.

The final-zeroed lower-left source family entering `Early` is zero on that
only edge, so the early lower-left tail is the terminal zero tail:

```text
Early(z) = 0,
dEarly_z(v) = 0.
```

The terminal top residual product is the single solved top-left block.  For
`M = 0`, `Last(y)` is definitionally/simp-reducibly the one-edge product

```text
coord_y.solvedA1 0 = coord_y.Ctop,
```

so `dLast_z(v)` is the Ctop-coordinate tangent.

Thus the landed `F3` bridge reduces to

```text
Dzv.F3 + coord.F3 * dCtop_z(v) = formal.F3.
```

For `M = 0`, the landed target-staged Ctop endpoint formula defines

```text
targetCtop =
  Dzv.Ctop
    - targetXsuccF2(0) * coord.solvedA3(0)
    - coord.F2(0.succ) * rawEdgeTupleA3(Dzv,0),
```

where

```text
targetXsuccF2 = retainedPassiveTargetRecoveredSuccessorF2At(z,Dzv).
```

It proves

```text
targetCtop = formal.Ctop.
```

The target-staged Ctop equality gives `targetCtop = formal.Ctop`.  The formal
`Ctop` recovery theorem gives `Tail * targetCtop = v.Ctop`, and in `M = 0`
the passive top-left tail is the empty product.  Thus the one-edge recovery
reads

```text
targetCtop = v.Ctop.
```

Substitute this into the reduced `F3` bridge:

```text
Dzv.F3 + coord.F3 * targetCtop = formal.F3.
```

Equivalently,

```text
Dzv.F3
  + coord.F3 *
      (Dzv.Ctop
        - targetXsuccF2(0) * coord.solvedA3(0)
        - coord.F2(0.succ) * rawEdgeTupleA3(Dzv,0))
= formal.F3.
```

Applying formal `F3` recovery gives

```text
(Dzv.F3 + coord.F3 * targetCtop) * (-(coord.Ctop))^{-1} = v.F3.
```

The right inverse factor is the negative terminal solved top-left block.  In
the one-edge case this is `-coord.Ctop`, not the passive tail used in Ctop
recovery.

## Boundary checks

- `rawEdgeTupleA3(Dzv,0)` is not asserted to be zero.  It occurs only under
  multiplication by the terminal zero extended `F2` slot inside `targetCtop`.
- The theorem uses the target-recovered successor `F2` family; it is not the
  earlier source-staged Ctop formula.
- The one-edge theorem avoids the unproved positive-tail derivative recurrence
  for `Early`.
- The determinant-chart hypothesis is still required by the existing Ctop and
  F3 recovery theorems.

## Positive-tail frontier

For `0 < M`, `Last` is the final passive top factor and should have a simpler
terminal-product derivative than `Early`.  The hard term is `dEarly`: its
honest recurrence must differentiate a noncommutative summand containing a
`C` residual product, the final-zeroed lower-left factor, and an inverse
top-product.  That recurrence is not proved in Lean yet.

## Kill conditions

- If `Early` fails to reduce to the zero terminal tail in the one-edge case,
  this slice is not Lean-ready.
- If `Last` is confused with the passive `Tail`, the recovery factor is wrong.
- If the theorem identifies the terminal raw lower-left target derivative with
  zero, it overclaims.
- If the statement still contains source tangents after target staging, it is
  not the intended target-side slice.
- If the result is read as positive-tail `F3` target staging, determinant-one
  target-side shear, determinant equality, measure transport, normal crossings,
  pole order, or RLCT, it overclaims.

## Nonclaims

No positive-tail `F3` target staging, no derivative recurrence for `Early`, no
whole-tuple target-side normalization, no determinant-one `LinearEquiv`, no
actual derivative determinant formula, no measure transport, no normal
crossings, no pole order, and no RLCT follows from this one-edge F3 slice.
