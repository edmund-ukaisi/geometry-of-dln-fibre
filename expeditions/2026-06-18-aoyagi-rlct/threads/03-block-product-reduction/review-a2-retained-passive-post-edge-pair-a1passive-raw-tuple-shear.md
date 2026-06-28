# Review - A2 post-edge-pair `A1passive` raw-tuple shear

Reviewer: xhigh `James the 2nd`

Verdict: PASS.  No required fixes.

## Checks

- The post-edge-pair `A1passive` shear uses the formal `(F2,C)` inverse
  `retainedPassiveFormalRawF2CLinearEquivAt ... .symm.toLinearMap.comp` in
  the correction map, not `retainedPassiveTargetRecoveredSuccessorF2At`.
- The determinant-one theorem is correctly scoped as an upper product shear on
  `A1passive × rest`: the equivalence is defined with
  `M := retainedPassiveRawA1PassiveFamily` and
  `N := retainedPassiveRawA1passiveRestFamily`, then determinant one follows
  from `linearEquivUpperShear_det_eq_one`.
- The notes do not overclaim full target normalizer, actual Frechet
  determinant equality, measure transport, normal crossings, pole order, or
  RLCT.
- The generic `linearEquivUpperShear_symm_apply` theorem is an `rfl` simp
  theorem matching the existing inverse definition, with low API risk and no
  apparent simp loop against `linearEquivUpperShear_apply`.

The reviewer kept the pass read-only and did not rerun Lean builds.
