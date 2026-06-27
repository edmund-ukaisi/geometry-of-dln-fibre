# Statement Card - A2 target-only lower-left step core

## Lean names

In `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetRecoveredSourceCtopAt
retainedPassiveTargetRecoveredSourceCtopAt_fderiv_eq_sourceCtop
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_zero
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_succ
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_fderiv_eq_source
retainedPassiveLowerLeftTailTargetOnlyStepCoreAt
retainedPassiveLowerLeftTailTargetOnlyStepCoreAt_fderiv_eq_sourceStepCore
```

## Mathematical content

The `Ctop` helper packages the already-landed recursive target-staged first
top-left branch as a target-side recovered source `Ctop` tangent.  On an actual
raw-order derivative target it recovers the source `Ctop` tangent.

The current solved-`A1` helper is target-only.  Its zero branch uses the
recovered source `Ctop` and the target-staged passive `A1` tail derivative.
Its successor branch uses the target-staged passive `A1` tangent.  On actual
raw-order derivative targets it agrees with the existing source-direction
current solved-`A1` tangent.

The target-only lower-left step core preserves the existing one-step
noncommutative matrix order and replaces only:

```text
v.C(r)      -> retainedPassiveTargetRecoveredSourceCAt hz w r,
v.A3free(q) -> rawEdgeTupleA3 w q.castSucc.
```

The theorem compares this target step core on actual raw-order derivative
targets with the existing source step core, keeping `dCnext`, `dAcur`,
`dPsucc`, and `dNext` explicit.

## Dependencies

```text
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
retainedPassiveTargetRecoveredSourceCAt_fderiv_eq_sourceC
retainedPassiveTargetStagedA1passiveTangentAt_fderiv_eq_source
fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply
retainedPassiveLowerLeftTailStepCoreAt
rawEdgeTupleA3_castSucc
rawEdgeTupleA3_topologyTupleEdgeRawOrder
```

## Non-claims

This is not the full target-only lower-left recursive derivative.  It does not
target-stage `dCnext`, construct a determinant-one target normalizer, prove a
Jacobian determinant formula, transport source priors, prove normal crossings,
compute pole order, or extract the RLCT.
