# Review - A2 retained-passive lower-left step core

Reviewer: xhigh `Averroes the 2nd`.

Verdict: PASS.  No findings.

## Scope

Reviewed the Lean additions:

```text
retainedPassiveLowerLeftTailStepCoreAt
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_stepCore_apply
fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_stepCore_apply
fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_stepCore_apply
```

and the companion reproduction/statement-card artifacts:

```text
reproduction-a2-retained-passive-recursive-target-staged-lower-left-tail.md
statement-card-a2-retained-passive-lower-left-step-core.md
```

## Findings

No findings.

The helper is a one-step RHS only.  The reviewer checked that `dG` remains
`v.2.2.1 q`, while the `C` tangent appears separately as `v.2.2.2.1 r`, and
that the matrix order matches the existing recurrence:

```text
Cprod * A3p * Pcast^-1 * (...) * Pcast^-1.
```

The generic, zero, and successor step-core theorems are definitional
restatements via `simpa` from the existing proved recurrences.

The successor branch uses

```text
u := s.castSucc
v.1 u
```

and not `v.1 s.succ` or `v.1 q`.  The underlying successor specialization
already proves the `u.succ = p` alignment with `Fin.succ_castSucc s` before
applying the solved-`A1` derivative lemma.

The statement card's nonclaims explicitly avoid the full recursive
target-staged derivative and determinant-normalizer claims.

## Review command note

The reviewer did not run Lean/build commands.  Controller verification ran
separately.
