# Reproduction - A2 Retained-Passive Ctop and F3 Recovery Consumers

Date: 2026-06-27.

Status: Lean-proved recovery consumer; independent implementation review
passed after the determinant-chart hypothesis was made explicit in the claim
surface.

## Setup

Let

```text
raw   = topologyTupleEdgeRawOrder,
data  = ofTopologyTuple z,
coord = data.toCoordinateData,
Dzv   = d(raw)_z(v),
Tail  = retainedPassiveA1TailAfterFirst data.A1seed.
```

Assume throughout that

```text
z in topologyTupleDetChartSet.
```

This is the retained-passive determinant chart hypothesis.  It supplies the
determinant-unit facts used by the formal recovery theorems below.

The formal retained-passive raw-order Jacobian at `z` has two already-proved
recovery laws:

```text
Tail * formal(z)(v).Ctop = v.Ctop,
formal(z)(v).F3 * (-(coord.solvedA1 last))^{-1} = v.F3.
```

The first law uses determinant-unitness of the passive tail.  The second uses
determinant-unitness of the terminal solved top-left block.

## Ctop Consumer

The landed Ctop tail-substitution theorem says that the staged Ctop expression
equals the formal Ctop component.

For `M=0`, the tail derivative term vanishes:

```text
U_Ctop =
  Dzv.Ctop
    - XsuccF2(0) * coord.solvedA3(0)
    - coord.F2(1) * XsuccA3(0)
  = formal(z)(v).Ctop.
```

Multiplying this equality on the left by `Tail` and applying formal recovery
gives

```text
Tail * U_Ctop = v.Ctop.
```

For `0 < M`, write `q=0 : Fin M`, `p=q.succ`, and

```text
Psucc(y) =
  residualFactorProduct (ofTopologyTuple y).A1seed (Fin.last (M+1)) p.succ.
```

The landed positive-tail Ctop theorem says

```text
U_Ctop =
  Dzv.Ctop
    - XsuccF2(0) * coord.solvedA3(0)
    - coord.F2(1) * XsuccA3(0)
    + Tail^{-1}
        * ((d Psucc)_z(v) * data.A1seed(p)
             + Psucc(z) * v.A1passive(q))
        * Tail^{-1}
        * coord.Ctop
  = formal(z)(v).Ctop.
```

Again, multiplying by `Tail` and applying formal recovery gives

```text
Tail * U_Ctop = v.Ctop.
```

This is a recovery consumer of the staged Ctop expression.  It does not
iterate the suffix derivative `(d Psucc)_z(v)`.

## F3 Consumer

The landed F3 component bridge has the form

```text
U_F3 =
  Dzv.F3
    - (d Early)_z(v) * Last
    + (coord.F3 - Early(z)) * (d Last)_z(v)
  = formal(z)(v).F3.
```

Here `Early` is the lower-left product-tail sum with the terminal lower-left
source zeroed, and `Last` is the terminal one-edge top-left residual factor.
Formal recovery gives

```text
U_F3 * (-(coord.solvedA1 last))^{-1} = v.F3.
```

The terminal factor is `coord.solvedA1 (Fin.last M)`, not the first-edge
passive tail.  For `M=0`, this is `coord.Ctop`.

## Kill Conditions

- If the Ctop recovery omits the left multiplication by `Tail`, it does not
  match the formal recovery law.
- If the positive Ctop correction changes sign or moves outside the two
  `Tail^{-1}` factors, the staged expression no longer matches the landed
  Ctop theorem.
- If the F3 recovery uses the passive tail instead of the terminal solved
  top-left block, the terminal factor is wrong.
- If this slice is described as a closed finite-sum formula for `dTail` or as
  full F3 source staging, it overclaims.

## Nonclaims

No closed finite-sum formula for `dTail`, no derivative formula for the lower
left early tail, no full source-staged tuple theorem, no target-side
determinant-one linear equivalence, no determinant equality, no measure
transport, no normal crossings, no pole order, and no RLCT statement is proved
by this slice.
