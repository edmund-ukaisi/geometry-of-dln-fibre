# Reproduction - A2 retained-passive F3 positive-tail target-only dEarly

Date: 2026-06-28.

Status: controller pen-and-paper reproduction for the next narrow Lean rung.

This note is independent of the quiver-based paper.  It records the elementary
substitution that makes the positive-tail terminal `F3` bridge use only
target-side staged data in its `dEarly` slot.

## Setup

Work in positive-tail shape

```text
z, w : RetainedPassiveRawTopologyTuple (M := M+1) rho kappa' R,
kappa' : Fin ((M+1)+2) -> Type.
```

For an actual raw-order derivative target, write

```text
Dzv = D_z topologyTupleEdgeRawOrder(v).
```

The already-landed positive-tail `F3` bridge has the form

```text
Dzv.F3
  - dEarly * solvedA1(last)
  + (F3_z - Early_z) * dLast#
= formal.F3,
```

where

```text
dLast# =
  Dzv.A1(qLast)
  - XsuccF2(qLast.succ) * solvedA3(qLast.succ)
  - F2(qLast.succ.succ) * rawA3(Dzv, qLast.succ),
```

with `qLast : Fin (M+1) := Fin.last M`.  This `dLast#` factor is already a
target-side expression: it uses the target-recovered successor `F2` family,
the target raw lower-left readout, and fixed coordinates of `z`.

The remaining source-parametrized term is

```text
dEarly =
  retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
    (M := M) z v 0.
```

## Target-only substitution

The previous checkpoint proved the target-only lower-left recursion and the
comparison theorem

```text
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
    (M := M) hz Dzv 0
=
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
    z v 0.
```

Therefore in the positive-tail `F3` bridge we may replace the source-staged
`dEarly` by

```text
dEarly# =
  retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
    (M := M) hz Dzv 0.
```

The resulting expression is

```text
Dzv.F3
  - dEarly# * solvedA1(last)
  + (F3_z - Early_z) * dLast#
= formal.F3.
```

No product order changes.  In particular, the substituted target-only `dEarly#`
is still left-multiplied by `solvedA1(last)` in the exact order

```text
- dEarly# * solvedA1(last).
```

## Recovery

The usual formal recovery theorem says that right-multiplying the displayed
formal `F3` branch by

```text
(-solvedA1(last))^-1
```

recovers the source `F3` tangent.  Thus the same target-only `dEarly#`
substitution gives

```text
(Dzv.F3
  - dEarly# * solvedA1(last)
  + (F3_z - Early_z) * dLast#)
  * (-solvedA1(last))^-1
= v.F3.
```

## Lean target

Expected Lean names:

```text
F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

## Dependencies

```text
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged
```

## Kill Conditions

- Do not shift the target-only lower-left call away from index `0`.
- Do not use the older `retainedPassiveLowerLeftProductTailTargetStagedFDerivAt`
  in the final displayed statement.
- Do not alter the `dLast#` target expression.
- Do not commute matrix factors in `- dEarly# * solvedA1(last)`.
- Do not claim a target-side linear equivalence, determinant-one normalizer,
  determinant equality, measure transport, normal crossings, pole order, or
  RLCT from this substitution.
