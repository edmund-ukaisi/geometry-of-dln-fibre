# Review - A2 post-`Ctop` recursive `dEarly` comparison

Reviewer: `Ohm the 2nd`, xhigh read-only reviewer.

Verdict: PASS.

Scope:

- `retainedPassivePostCtopCnextFDerivLinearMapAt_after_T123_eq_targetStaged`
- `retainedPassivePostCtopLowerLeftTailStepCoreLinearMapAt_apply`
- `retainedPassivePostCtopLowerLeftTailStepCoreLinearMapAt_after_T123_eq_targetOnly`
- `retainedPassivePostCtopLowerLeftProductTailFDerivLinearMapAt_after_T123_eq_targetOnly`
- expedition-note claims around this checkpoint.

Findings:

- The `Cnext` comparison uses the post-`Ctop` suffix bridge at `r.succ` with
  `r := q.succ`, matching the target-staged `Cnext` index.
- The one-step comparison uses `Dzv` for target recovery and bridges
  post-`Ctop` source `C` through
  `retainedPassivePostCtopSourceCAtLinearMapAt_after_T123_eq_targetRecovered`;
  it does not apply pre-edge target recovery to post-`Ctop` data.
- The index roles are consistent: `q.castSucc` selects the non-final passive
  `A3` block, `q.succ` selects the current `C` edge, and `p.succ.val` selects
  the solved-`A1` suffix start.
- The product-tail induction uses the successor induction hypothesis exactly as
  the `dNext` comparison and unfolds both recursions at the same `n`.
- The notes do not claim the positive-tail `F3` shear, determinant package,
  full target normalisation, measure transport, normal crossings, pole order,
  or RLCT.

Checks reported by reviewer:

```text
git diff --check: passed
scripts/sorries: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
forbidden-marker search in touched Lean file: no hits
```

The reviewer did not independently complete the focused Lean build because the
read-only subagent could not use the shared build semaphore path. The
controller completed the focused build separately.
