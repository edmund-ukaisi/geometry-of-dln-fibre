# Statement Card - A2 Retained-Passive Formal Non-Edge Recovery

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

## Lean Names

```text
retainedPassiveFormalRawOrderJacobianAt_recovers_A1passive
retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop
retainedPassiveFormalRawOrderJacobianAt_recovers_F3
```

## Reproduction

```text
reproduction-a2-retained-passive-formal-nonedge-recovery.md
```

## Claim

For `u = retainedPassiveFormalRawOrderJacobianAt z v`, the formal map recovers
the non-edge branches by:

```text
u.A1passive_p = v.A1passive_p,
Tail * u.Ctop = v.Ctop,
u.F3 * (-(coord.solvedA1 (Fin.last M)))⁻¹ = v.F3.
```

The `Ctop` and `F3` formulas use the determinant-chart hypothesis to cancel
`Tail^{-1}` and `(-Last)^{-1}` respectively.

## Proof Plan

1. Unfold `retainedPassiveFormalRawOrderJacobianAt` and use
   `retainedPassiveFormalRawOrderJacobian_apply`.
2. `A1passive` is projection-level.
3. For `Ctop`, derive `IsUnit Tail.det` from the determinant-chart passive
   `A1` units and apply `Matrix.mul_nonsing_inv_cancel_left`.
4. For `F3`, derive `IsUnit (coord.solvedA1 (Fin.last M)).det`, convert it to
   `IsUnit (-Last).det`, and apply `Matrix.mul_nonsing_inv_cancel_right`.

## Review

```text
review-a2-retained-passive-formal-nonedge-recovery.md
```

## Status

Implemented in Lean.  Focused and full builds passed.  `scripts/sorries` and
`git diff --check` passed.  The new recovery theorems depend only on
`[propext, Classical.choice, Quot.sound]`.  Independent xhigh review passed.

## Nonclaims

This is formal inverse bookkeeping only.  It is not `Ctop`/`F3` source staging,
not a target-side determinant-one equivalence, not determinant equality for the
actual derivative, and not a measure, normal-crossing, pole-order, or RLCT
result.
