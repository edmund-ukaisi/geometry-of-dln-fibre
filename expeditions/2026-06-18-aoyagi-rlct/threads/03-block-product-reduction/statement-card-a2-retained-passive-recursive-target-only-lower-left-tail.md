# Statement Card - A2 recursive target-only lower-left tail

## Lean names

Expected in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
retainedPassiveSolvedA1_residualFactorProduct_eq_A1seed_of_pos
```

Expected in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveSolvedA1TargetStagedTangentAt
retainedPassiveSolvedA1TargetStagedTangentAt_zero
retainedPassiveSolvedA1TargetStagedTangentAt_succ
retainedPassiveSolvedA1TargetStagedTangentAt_fderiv_eq_source
retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_self
retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_step
retainedPassiveSolvedA1SuffixProductAt
fderiv_retainedPassive_solvedA1_residualFactorProduct_targetStaged_apply
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_self
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_step
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_zero
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_succ
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged
fderiv_retainedPassiveLowerLeftProductTailSum_targetOnly_apply
```

## Mathematical Content

This defines a target-only recursive derivative for the retained-passive
zeroed-final lower-left product tail:

```text
D^o_{M+1} = 0,
D^o_n =
  StepWithCnext(q, dAcur#, dPsucc#, D^o_{n+1}).
```

The current solved-`A1` tangent, the stored `C` tangent, the `Cnext` suffix
derivative, the solved-`A1` suffix derivative `dPsucc`, and the successor
lower-left derivative are all supplied by target-side staged expressions.

On actual raw-order derivative targets, the target-only recursion agrees with
the existing source-direction staged lower-left recursion.  Combining this
with the already-landed source-staged actual-derivative bridge gives the
Frechet derivative of the zeroed-final lower-left tail as the target-only
recursive expression.

## Dependencies

```text
retainedPassiveSolvedA1_residualFactorProduct_eq_A1seed_of_pos
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_fderiv_eq_source
retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt_fderiv_eq_sourceStepCore
fderiv_retainedPassive_solvedA1_residualFactorProduct_targetStaged_apply
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply
```

## Non-Claims

This is not a determinant-one target normalizer.  It does not prove a Jacobian
determinant equality, source-prior transport, inverse-density pushforward,
normal crossings, pole order, or RLCT.  It also does not prove analytic
normal-crossing extraction.
