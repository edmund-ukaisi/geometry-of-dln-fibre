# Review - A2 residual zero-locus handoff

Date: 2026-06-25.

Reviewer: xhigh subagent Bacon the 5th.

Scope:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-residual-zero-locus-handoff.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-residual-zero-locus-handoff.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/thread.md
expeditions/2026-06-18-aoyagi-rlct/priorities.md
```

## Findings

No blocking findings.

The generic measure lemma is mathematically sound.  For a nonnegative real
function, the set where strict positivity fails is contained in the zero locus,
so nullity of the zero locus gives a.e. positivity by measure monotonicity.

The residual specialization is correctly scoped.  It assumes nullity under
`μ.restrict source` and uses only the existing finite square-sum nonnegativity
fact for the residual coordinate square-sum.

The combined monotonicity helper keeps the right dependency shape:
`source' ⊆ source`, residual zero-locus nullity on the larger restricted source,
and finite residual negative-power integral on the larger source remain
explicit inputs.  Only residual positivity is derived before applying the
existing restriction helper.

The documentation does not overclaim.  The reproduction, statement card,
thread, and priorities entries all keep residual zero-locus nullity, residual
negative-power integrability, source/chart measure transport, original-loss
comparison, density/Jacobian transport, normal crossings, pole order, and RLCT
out of scope.

## Verdict

Approved as mathematically and formalisation-scope sound.

The reviewer performed a read-only source review and did not edit files.  The
controller ran the Lean build gates separately.
