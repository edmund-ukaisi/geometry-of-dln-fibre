# Review - A2 retained-passive recursive target-staged lower-left tail

Reviewer: xhigh `Turing the 2nd`.

Verdict: PASS.  No findings.

## Scope

Reviewed the Lean recursive API:

```text
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt_zero
retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt_succ
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_self
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_step
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_zero
retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_succ
```

and the companion statement card:

```text
statement-card-a2-retained-passive-recursive-target-staged-lower-left-tail.md
```

## Findings

No findings.

Checked points:

- The recursive base is `m = M + 1`, with value `0`.
- The successor current tangent unfolds to `v.1 s.castSucc`, not
  `v.1 s.succ`.
- The recursive successor value is passed as the final
  `retainedPassiveLowerLeftTailStepCoreAt` argument.
- The new statements are expression/unfold equalities only.  They do not assert
  equality with the actual `fderiv` of
  `retainedPassiveLowerLeftProductTailSum`, and they do not claim a determinant
  normalizer.

## Review command note

The reviewer did not run Lean/build commands.  Controller verification ran
separately.
