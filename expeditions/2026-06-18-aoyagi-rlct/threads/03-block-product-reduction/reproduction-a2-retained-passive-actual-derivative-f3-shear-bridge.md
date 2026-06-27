# Reproduction - A2 retained-passive actual derivative F3 shear bridge

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; independent xhigh check PASS;
Lean reconnaissance PASS; Lean bridge proved.

This note is independent of the quiver-based paper.  It uses only the
retained-passive terminal lower-left solve isolated in the Aoyagi local product
reduction.

## Setup

Work in the retained-passive raw-order map

```text
raw = topologyTupleEdgeRawOrder.
```

At a tuple `z`, write

```text
data  = ofTopologyTuple z,
coord = data.toCoordinateData,
A     = coord.solvedA1,
G     = coord.solvedA3,
```

and define the terminal top-left product and earlier lower-left tail by

```text
LastTop =
  residualFactorProduct A (Fin.last (M+1)) (Fin.last M).castSucc
    (Fin.last M).castSucc.le_last,

Early =
  retainedPassiveLowerLeftProductTailSum
    A (retainedPassiveA3WithoutLast data.A3seed) data.C
    0 (Nat.zero_le (M+1)).
```

The terminal solved lower-left block is

```text
G_last = coord.solvedA3 (Fin.last M)
       = -(coord.F3 - Early) * LastTop.
```

Here `LastTop = coord.solvedA1 (Fin.last M)` in the one-edge final factor
sense used by `retainedPassiveFormalRawOrderJacobianAt`: for `M > 0` it is the
final passive top-left block, while for `M = 0` the passive tail is empty and
`LastTop = coord.solvedA1 0 = coord.Ctop`.

For a tangent vector `v`, abbreviate Frechet differentials at `z` by

```text
dF3 = v.F3,
dE  = d(Early)(v),
dL  = d(LastTop)(v).
```

## Raw Formula

The raw terminal lower-left target is

```text
Y21_last = G_last = -(F3 - Early) * LastTop.
```

## Calculation

Differentiate:

```text
dY21_last
  = -d(F3 - Early) * LastTop - (F3 - Early) * dLastTop
  = -dF3 * LastTop + dE * LastTop - (F3 - Early) * dL.
```

Therefore

```text
dY21_last - dE * LastTop + (F3 - Early) * dL
  = -dF3 * LastTop
  = dF3 * (-LastTop).
```

In tuple notation, the intended component theorem is

```text
((D raw z) v).F3
  - d(Early)(v) * LastTop
  + (coord.F3 - Early) * d(LastTop)(v)
= v.F3 * (-LastTop).
```

The matrix order is forced: `F3`, `Early`, and `dE` have shape
`kappa'(Fin.last (M+1)) x rho`, while `LastTop` and `dLastTop` are square
`rho x rho` matrices.

## Formal Raw-Order Comparison

The transported formal raw-order Jacobian sends the raw `F3` tangent to

```text
v.F3 * (-(coord.solvedA1 (Fin.last M))).
```

The `LastTop` definition above is the residual-factor product used in the
terminal solve and agrees with this final solved top-left factor.  Thus the
sheared actual derivative component should agree with the `F3` component of
`retainedPassiveFormalRawOrderJacobianAt z v`.

## Guardrails

- This is the terminal lower-left coordinate only; it complements the passive
  `A3` identity but does not subsume it.
- The correction `- d(Early)(v) * LastTop` is essential.  It removes variation
  of earlier passive lower-left coordinates and residual blocks.
- The correction `+ (coord.F3 - Early) * d(LastTop)(v)` is essential.  It
  removes variation of the terminal top-left factor.
- `LastTop` is not the first-edge passive tail `Tail` used by the `Ctop`
  bridge.
- This does not assemble a global determinant-one shear linear equivalence,
  determinant equality, measure pushforward, normal crossings, pole order, or
  RLCT.

## Independent Checks

`Epicurus the 5th`, xhigh read-only pen-and-paper reviewer, returned PASS and
confirmed the formula, signs, right-multiplication order, `M = 0` boundary,
and `LastTop` versus `Tail` distinction.

`Godel the 5th`, xhigh read-only Lean reconnaissance scout, confirmed the
existing APIs for `topologyTupleEdgeRawOrder_F3`, `retainedPassiveSolvedA3_last`,
the early-tail and terminal-top differentiability helpers, and the formal
raw-order terminal component `v.F3 * (-LastTop)`.

After implementation, `Jason the 5th`, xhigh read-only explorer, independently
checked the Lean proof shape and orientation.  The follow-up confirmed that the
right-multiplication order, signs, and `M = 0` endpoint behavior match the
calculation above.
