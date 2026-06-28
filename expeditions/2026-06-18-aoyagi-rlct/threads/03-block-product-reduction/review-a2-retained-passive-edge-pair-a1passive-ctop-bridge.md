# Review: A2 retained-passive edge-pair, `A1passive`, and `Ctop` bridge

Reviewer: xhigh `Popper the 2nd`.

Verdict: PASS.  No required fixes.

## Scope

Reviewed the post-`A1passive` `Ctop` shear and the composed
edge-pair -> `A1passive` -> `Ctop` bridge in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean` against the
reproduction note
`reproduction-a2-retained-passive-post-a1passive-ctop-shear.md`.

## Checked Lean Surface

```text
retainedPassivePostA1passiveTailFDerivLinearMapAt_step_apply
retainedPassivePostA1passiveTailFDerivLinearMapAt_fderiv_after_T12_eq_targetStaged
retainedPassivePostA1passiveCtopCorrectionLinearMapAt_apply
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt_apply
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt_det_eq_one
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt_Ctop
retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt_F2C
rawEdgeTupleA3_retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairThenA1passiveThenCtopShear_fderiv_Ctop_eq_formalRawOrderJacobianAt
```

## Findings

No findings.

The shear formula matches the target-staged `Ctop` theorem.  It uses

```text
u.Ctop
  - Xsucc 0 * coord.solvedA3 0
  - coord.F2 0.succ * rawEdgeTupleA3 u 0
  + Tail^-1 * D_0(u) * Tail^-1 * coord.Ctop,
```

not the `Tail * (...)` source-recovery coordinate.

The determinant-one claims are scoped as raw-tuple linear-equivalence shear
determinant claims.  No new theorem feeds this partial bridge into the
conditional actual-Frechet-determinant theorem or claims actual Frechet
determinant equality.

The composed bridge proves only the `Ctop` component agreement.  It preserves
the nonclaims: no `F3` agreement, no full raw-tuple equality, no normal-crossing
claim, and no RLCT claim.

The reviewer checked the two specific failure modes: no pre-edge-pair target
recovery is applied to post-edge-pair data in the new `Ctop` shear, and no
`Tail`-multiplied source recovery is used as the determinant-one `Ctop`
coordinate.

## Reviewer Verification

The reviewer ran `lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`
from the `lean/` Lake root and `git diff --check -- lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`;
both passed.
