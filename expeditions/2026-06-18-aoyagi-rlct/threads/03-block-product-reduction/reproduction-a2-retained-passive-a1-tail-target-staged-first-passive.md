# Reproduction - A2 retained-passive A1-tail first passive target staging

Date: 2026-06-27.

Status: reproduced; Lean helper, positive-tail wrapper, Ctop consumer, and
Ctop recovery companion proved; xhigh independent review passed.

This note is independent of the quiver-based paper.  It records a narrow
target-staging step for the passive top-left suffix derivative that appears in
the retained-passive `Ctop` and `F3` formulas.

## Setup

Work at positive retained-passive tail length `M`, with `hM : 0 < M`.  Let

```text
raw = topologyTupleEdgeRawOrder,
data = ofTopologyTuple z,
coord = data.toCoordinateData,
Dzv = (fderiv raw z) v.
```

The derivative theorem for the first passive top-left suffix sets

```text
q = <0, hM> : Fin M,
p = q.succ  : Fin (M+1).
```

Thus `q` is the first passive top-left source coordinate and `p` is the first
seed factor in the retained passive tail after the solved first block.  Define
the remaining suffix

```text
Psucc(y) =
  residualFactorProduct
    (A1seed(y)) (Fin.last (M+1)) p.succ.
```

The landed derivative theorem gives

```text
dTail =
  (fderiv Psucc z) v * data.A1seed p
  + Psucc(z) * v.A1passive(q).
```

## Target Replacement

The target-staged passive `A1` recovery theorem gives

```text
v.A1passive(q) =
  Dzv.A1passive(q)
  - XsuccF2(q.succ) * coord.solvedA3(q.succ)
  - coord.F2(q.succ.succ) * rawEdgeTupleA3(Dzv, q.succ),
```

where

```text
XsuccF2 = retainedPassiveTargetRecoveredSuccessorF2At(z, Dzv).
```

Substituting only this equality into the first-passive term gives the intended
helper:

```text
dTail =
  (fderiv Psucc z) v * data.A1seed p
  + Psucc(z) *
      (Dzv.A1passive(q)
        - XsuccF2(q.succ) * coord.solvedA3(q.succ)
        - coord.F2(q.succ.succ) * rawEdgeTupleA3(Dzv, q.succ)).
```

The residual derivative `(fderiv Psucc z) v` is left explicit.  No suffix
recursion, terminal cleanup, or finite-sum formula is part of this slice.

## Ctop Consumer

The current positive-tail target-staged `Ctop` formula contains

```text
Tail^-1 *
  ((fderiv Psucc z) v * data.A1seed p + Psucc(z) * v.A1passive(q))
  * Tail^-1 * coord.Ctop.
```

The immediate consumer replaces only `v.A1passive(q)` by the target expression
above, preserving the outer factor order:

```text
Tail^-1 *
  ((fderiv Psucc z) v * data.A1seed p
    + Psucc(z) * targetA1(q))
  * Tail^-1 * coord.Ctop.
```

This removes one explicit source tangent from the `Ctop` bridge without
claiming full target staging of the passive suffix.

## Boundary Cases

For `M = 0`, there is no `q : Fin M`; the existing zero-tail `Ctop` theorem is
the boundary case.

For `M = 1`, `Psucc` is an empty suffix and
`coord.F2(q.succ.succ)` is terminal zero.  This theorem does not simplify
either fact; it only records the target-staged replacement of
`v.A1passive(q)`.

For `M > 1`, `(fderiv Psucc z) v` still contains later passive suffix
derivatives.  That residual is intentional.

## Lean Scope

Lean targets in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_target_staged_apply
fderiv_retainedPassive_A1TailAfterFirst_pos_target_staged_apply
Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

Dependencies:

- `fderiv_retainedPassive_A1TailAfterFirst_pos_apply`;
- `A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive`;
- existing positive-tail target-staged `Ctop` theorem for the consumer.

## Kill Conditions

- Do not state this for `M = 0`.
- Do not use the Ctop edge index `0 : Fin (M+1)` in place of
  `q.succ : Fin (M+1)` for the passive `A1` target replacement.
- Do not identify the terminal raw lower-left readout with zero; it may only
  be killed under the terminal zero extended `F2` factor in other theorems.
- Do not simplify `(fderiv Psucc z) v`, even in the `M = 1` boundary.
- Do not commute matrix factors or move the outer `Tail^-1` factors.
- Do not claim full `Ctop` or `F3` target staging, determinant equality,
  measure transport, normal crossings, pole order, or RLCT.
