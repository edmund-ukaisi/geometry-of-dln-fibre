# Reproduction - A2 Retained-Passive F3 Target-Staged Shear

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before Lean formalisation.

## Setup

The existing terminal `F3` shear theorem says that, for the retained-passive
raw-order map,

```text
D(raw F3)
  - dEarly * LastTop
  + (F3 - Early) * dLastTop
= dF3 * (-LastTop).
```

Here

```text
Early(y) =
  retainedPassiveLowerLeftProductTailSum
    solvedA1(y) retainedPassiveA3WithoutLast(y) C(y) 0,

LastTop(y) =
  residualFactorProduct solvedA1(y)
    (Fin.last ...) (Fin.last ...).castSucc.
```

The theorem is a product-rule cancellation for

```text
raw F3 = -(F3 - Early) * LastTop.
```

It has the right formal terminal factor `dF3 * (-LastTop)`, but it still
contains the analytic derivative `dEarly`.

## Target-Staged Earlier Tail

The landed recurrence

```text
fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply
```

identifies the derivative of the zeroed-final lower-left tail with the
recursive target-staged expression

```text
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt z v m hm.
```

At the first tail index, this gives

```text
dEarly =
  retainedPassiveLowerLeftProductTailTargetStagedFDerivAt z v 0
    (Nat.zero_le ...).
```

Substituting this into the terminal `F3` shear yields

```text
D(raw F3)
  - targetStagedEarly * LastTop
  + (F3 - Early) * dLastTop
= dF3 * (-LastTop).
```

This is only a positive-tail wrapper: the Lean statement uses
`κ' : Fin ((M+1)+2) -> Type*`, so the existing `F3` shear is invoked with
`M+1` and the target-staged earlier-tail recurrence with `M`.

## Product-Order Check

No factor is commuted.  The staged earlier-tail derivative remains the left
factor in

```text
targetStagedEarly * LastTop.
```

The terminal top correction remains

```text
(F3 - Early) * dLastTop.
```

The formal output remains

```text
dF3 * (-LastTop).
```

## Kill Conditions

- If the staged earlier-tail derivative is multiplied on the right by
  `LastTop` in a different order, the statement no longer matches the
  product rule.
- If the theorem erases the `(F3 - Early) * dLastTop` correction, it is not
  the terminal `F3` shear.
- If the theorem is stated for arbitrary `κ' : Fin (M+2)` using the positive
  staged-tail recurrence, it mishandles the empty-tail boundary.
- If it is cited as determinant equality, target-side linear equivalence,
  measure transport, normal crossings, pole order, or RLCT, it overclaims.

## Nonclaims

This does not prove the full retained-passive analytic derivative equals the
formal raw-order Jacobian.  It does not compute a determinant, prove a
measure pushforward, produce normal crossings, compute pole order, or extract
an RLCT.
