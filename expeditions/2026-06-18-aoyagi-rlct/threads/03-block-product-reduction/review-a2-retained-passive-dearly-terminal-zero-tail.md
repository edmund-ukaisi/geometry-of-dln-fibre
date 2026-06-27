# Review - A2 retained-passive dEarly terminal zero tail

Date: 2026-06-27.

Reviewer: xhigh `Aquinas`.

Verdict: PASS.

## Scope

Reviewed the proposed terminal zeroed-tail theorem in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

against the reproduction and statement card:

```text
reproduction-a2-retained-passive-dearly-terminal-zero-tail.md
statement-card-a2-retained-passive-dearly-terminal-zero-tail.md
```

## Findings

No blocking issue.

The theorem
`fderiv_retainedPassiveLowerLeftProductTailSum_withoutLast_last_apply`
is correctly scoped to the terminal final-edge tail `M (Nat.le_succ M)`,
with the final `A3` block zeroed by `retainedPassiveA3WithoutLast`.

The map is pointwise constant zero by the algebraic lemma
`retainedPassiveLowerLeftProductTailSum_withoutLast_last`; the proof route is
to rewrite the function to zero and apply `fderiv_const_apply`.

No determinant-chart membership, differentiability of products, or
invertibility hypothesis is needed.  This is not a solved terminal `A3` or
`F3` derivative theorem, not source staging of `dCprod` or `dPcast`, and not
determinant, measure, normal-crossing, pole-order, or RLCT work.
