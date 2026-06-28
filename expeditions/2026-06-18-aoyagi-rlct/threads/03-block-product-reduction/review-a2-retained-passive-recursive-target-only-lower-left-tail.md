# Review - A2 retained-passive recursive target-only lower-left tail

Date: 2026-06-27.

Reviewer: xhigh `Meitner the 2nd`.

Verdict: PASS.

## Scope

Reviewed the uncommitted checkpoint adding:

```text
retainedPassiveSolvedA1_residualFactorProduct_eq_A1seed_of_pos
retainedPassiveSolvedA1TargetStagedTangentAt
retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
fderiv_retainedPassive_solvedA1_residualFactorProduct_targetStaged_apply
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged
fderiv_retainedPassiveLowerLeftProductTailSum_targetOnly_apply
```

The review was read-only.

## Checks

- The positive solved-`A1` residual-product lemma is scoped with
  `hmpos : 1 <= m`; it is not a zero-suffix statement.
- The lower-left target-only recursion uses the solved suffix derivative at
  `p.succ.val`, so `dPsucc` starts at the first factor of `Psucc`.
- The stored-`C` successor suffix remains the landed `Cnext` specialization
  beginning at `r.succ`, not at `r`.
- The terminal lower-left base is the zeroed-final endpoint `M+1`.
- The one-step core preserves the existing noncommutative matrix order and
  does not commute factors.
- The final theorem is a Frechet-derivative target-staging theorem only.  It
  does not claim a determinant-one target normalizer, determinant equality,
  measure transport, normal crossings, pole order, or RLCT.

## Hygiene

The reviewer also reported clean `git diff --check`, no proof-placeholder
markers in the two touched Lean files, and successful `lake env lean` checks
for the touched Lean files.  Controller verification separately ran the focused
module build, full `DLNFibre` build, forbidden-marker gates, and direct axiom
audits.
