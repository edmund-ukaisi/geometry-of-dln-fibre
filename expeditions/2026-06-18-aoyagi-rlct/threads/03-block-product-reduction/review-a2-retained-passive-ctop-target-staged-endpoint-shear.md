# Review - A2 retained-passive Ctop target-staged endpoint shear

Date: 2026-06-27.

Reviewer: Einstein, xhigh read-only checker.

Status: PASS.

## Verdict

The reproduction is mathematically sound and Lean-ready from the local Lean
facts checked.  The implemented Lean names are:

```text
Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

## Boundary Check

- In the `M = 0` case, the terminal raw lower-left derivative is used only in
  `coord.F2 q0.succ * rawEdgeTupleA3 Dzv q0`.
- The multiplied lower-left equality is justified by the terminal zero `F2`
  factor, not by identifying the raw derivative itself with zero.
- In the positive-tail case, the suffix derivative term keeps the landed order:

```text
Tail^{-1} * ((fderiv Psucc z) v * data.A1seed p + Psucc z * v.1 q)
  * Tail^{-1} * coord.Ctop
```

- The successor correction is the target-recovered family
  `retainedPassiveTargetRecoveredSuccessorF2At z Dzv`.
- The determinant-chart hypothesis remains explicit, and the positive-tail
  theorems keep `hM : 0 < M`.

## Nonclaims

This review does not certify `F3` target staging, whole-tuple target-side
normalization, determinant-one target-side shear, actual derivative determinant
equality, measure transport, normal crossings, pole order, or RLCT.

## Verification

Controller verification ran:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre
scripts/sorries
git diff --check
```

All passed.  Axiom audit for the four new theorem names reported only
`[propext, Classical.choice, Quot.sound]`.
