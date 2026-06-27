# Statement Card - A2 target-staged `C` suffix derivative

## Lean names

In `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveCTailTargetOnlyStepAt
retainedPassiveCTailTargetOnlyStepAt_fderiv_eq_sourceStep
retainedPassiveCSuffixTargetStagedFDerivAt
retainedPassiveCSuffixTargetStagedFDerivAt_self
retainedPassiveCSuffixTargetStagedFDerivAt_step
retainedPassiveCSuffixProductAt
fderiv_retainedPassive_C_residualFactorProduct_targetStaged_apply
retainedPassiveCnextTargetStagedFDerivAt
retainedPassiveCnextTargetStagedFDerivAt_fderiv_eq_source
retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt_fderiv_eq_sourceStepCore
```

## Mathematical content

This target-stages the Frechet derivative of stored `C` suffix products by the
elementary residual-product rule:

```text
D#_{M+1} = 0,
D#_m =
  D#_{m+1} * C_z(a)
  + S_{m+1}(z) * targetRecoveredC(a).
```

The one-step helper packages this product-rule step with an explicitly supplied
successor suffix derivative.  The recursive suffix derivative uses that helper
as its unfold API.

On actual raw-order derivative targets, the target-staged expression equals
the Frechet derivative of the suffix product.  The `Cnext` specialization is
the suffix beginning at `r.succ` in the positive-tail lower-left step.

The final wrapper feeds this staged `dCnext` into the already-landed
target-only lower-left step core, leaving the other supplied derivative slots
explicit.

## Dependencies

```text
fderiv_retainedPassive_C_residualFactorProduct_castSucc_apply
fderiv_retainedPassive_C_residualFactorProduct_self_apply
retainedPassiveTargetRecoveredSourceCAt_fderiv_eq_sourceC
retainedPassiveLowerLeftTailTargetOnlyStepCoreAt
retainedPassiveLowerLeftTailTargetOnlyStepCoreAt_fderiv_eq_sourceStepCore
```

## Non-claims

This is not the full recursive target-only lower-left derivative.  It does not
target-stage `dAcur`, `dPsucc`, or `dNext`, construct a determinant-one target
normalizer, prove a Jacobian determinant formula, transport source priors,
prove normal crossings, compute pole order, or extract the RLCT.
