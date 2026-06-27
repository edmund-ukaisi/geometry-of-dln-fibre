# Reproduction - A2 retained-passive target edge-pair recovery

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean proved; xhigh review
passed after documentation status repair.

This note is independent of the quiver-based paper.  It advances the retained-
passive raw-order Jacobian frontier by removing the source tangent from the
successor `F2` correction in the `(F2,C)` edge-family shear.  It is still only
the `(F2,C)` edge family.  It does not construct a determinant-one target-side
linear equivalence for the whole derivative.

## Setup

Work at a retained-passive raw tuple `z` in the determinant chart.  Write

```text
raw    = topologyTupleEdgeRawOrder,
coord  = (ofTopologyTuple z).toCoordinateData,
w      = a target raw tuple,
Dzv    = d(raw)_z(v),
formal = retainedPassiveFormalRawOrderJacobianAt(z)(v).
```

For a target tuple `w`, define the normalized edge pair from a supplied
successor `F2` value `Xsucc(q)` by

```text
U_F(q) =
  w.F2_q
  + rawEdgeTupleA1(w)_q * coord.F2 q.castSucc
  - Xsucc(q) * coord.C q,

U_C(q) =
  w.C_q
  + rawEdgeTupleA3(w)_q * coord.F2 q.castSucc.
```

The formal edge-pair inverse recovers the current source edge tangent from a
normalized pair by

```text
Frec(q) =
  coord.solvedA1(q)^-1 * (coord.F2(q.succ) * U_C(q) - U_F(q)),

Crec(q) =
  U_C(q) + coord.solvedA3(q) * Frec(q).
```

The determinant-chart hypothesis supplies invertibility of
`coord.solvedA1(q)` for every retained edge.

## Backward Target Recurrence

The successor correction should be determined from the target tuple itself by
descending over retained edges.

At the terminal edge `q = Fin.last M`, the retained-passive extended successor
`F2` slot is zero, so

```text
Xsucc(Fin.last M) = 0.
```

Define `Frec(Fin.last M)` by the formula above with this zero successor.  This
is exactly the terminal target-side recovery formula already proved.

For a nonterminal edge `q = p.castSucc`, the successor correction is the
recovered `F2` tangent at the next retained edge:

```text
Xsucc(q) =
  cast_{p.succ.castSucc = p.castSucc.succ}(Frec(p.succ)).
```

Then define `Frec(q)` by the same formal inverse formula.  This is a
well-founded backward recurrence because `Frec(p.succ)` is closer to the
terminal edge than `Frec(p.castSucc)`.

The corresponding all-edge successor family is

```text
targetXsucc =
  Fin.snoc
    (fun p : Fin M =>
      cast_{p.succ.castSucc = p.castSucc.succ}(Frec(p.succ)))
    0.
```

## Check on Actual Derivatives

Set `w = Dzv`.  We prove by downward induction on `q : Fin (M+1)` that

```text
Frec(q) = v.F2_q.
```

Terminal case: the recurrence uses `Xsucc = 0`, so the existing terminal
target-side theorem gives

```text
Frec(Fin.last M) = v.F2_(Fin.last M).
```

Nonterminal step: assume

```text
Frec(p.succ) = v.F2_(p.succ).
```

After the dependent cast, the target-defined successor correction equals the
source-staged successor correction:

```text
cast(Frec(p.succ)) = cast(v.F2_(p.succ)).
```

The existing nonterminal source-staged recovery theorem then gives

```text
Frec(p.castSucc) = v.F2_(p.castSucc).
```

Thus the target-defined successor family agrees with the earlier
source-staged successor family when `w = Dzv`.

## Target Edge-Pair Shear

Using the target-defined successor family, define

```text
targetPair(z,w) = (U_F, U_C).
```

For `w = Dzv`, the target successor family equals the source-staged successor
family.  Therefore the already-proved all-edge source-staged theorem gives

```text
targetPair(z,Dzv) = (formal.F2, formal.C).
```

Applying the formal edge-pair inverse gives the source-pair recovery

```text
(formalEdgePairEquivAt z)^-1 (targetPair(z,Dzv)) = (v.F2, v.C).
```

This is target-side for the `(F2,C)` successor correction, but the inverse
applied at the end is still the existing formal edge-pair inverse.  The
construction is not yet packaged as a determinant-one `LinearEquiv` on target
coordinates.

## Boundary Cases

- If `M = 0`, there are no nonterminal edges; the recurrence is only the
  terminal zero-successor case.
- The terminal zero is used only at `Fin.last M`, not at the edge immediately
  before the terminal edge.
- The nonterminal cast must transport from the recovered value at
  `p.succ.castSucc` to the extended successor slot `p.castSucc.succ`.

## Kill Conditions

- If the terminal branch uses a nonzero successor correction, it violates the
  retained-passive zero-extension convention.
- If a nonterminal branch uses zero instead of the recovered successor, it
  breaks the backward recurrence.
- If the dependent cast is omitted or reversed, the successor correction has
  the wrong target type.
- If the result is named as determinant equality, a determinant-one
  `LinearEquiv`, a measure-transport theorem, a normal-crossing theorem,
  pole-order theorem, or RLCT theorem, it overclaims.

## Nonclaims

No whole-tuple target-side normalization, no target-side determinant-one
linear equivalence, no determinant equality for the actual Frechet derivative,
no measure transport, no normal crossings, no pole order, and no RLCT follows
from this target edge-pair recovery.
