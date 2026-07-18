## Verdict

Block the rung‑1 fidelity spot-check. This is not a finiteness-soundness defect, but it is an encoded-fidelity defect.

### Q1

**FACT:** `StepRel` accepts an out-of-range case‑1 edge. Concrete witness:

- Parent: `numDiv = 1`, `divExp 0 = 5`, `resCols = 3`.
- Substitution: `runLen = 2`, `mergeIdx = 99`.
- Case 1(1) leaves the ledger unchanged, so a child with exponent `5` satisfies `StepRel` by `rfl`.
- The faithful in-range transition targeting divisor `0` would produce `5 + 2·3 = 11`.

This exact witness appears in [ScratchAxRung1.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev2/lean/DLNFibre/DLN/RLCT/Engine/ScratchAxRung1.lean:31).

**FACT:** The driver does not consume `StepRel`, so this does not weaken the finiteness conclusion.

**INFER:** A total arbitrary default is acceptable inside `stepUpdate` only if the relation restricts callers to its valid domain. Here it does not. “The construction never emits it” is unencoded intent and cannot support a passed fidelity certificate.

### Q2

The minimal sufficient fix is a case-applicability guard:

```lean
def StepApplicable (n : StepData M) (e : Edge M) : Prop :=
  match e.case with
  | .case11 | .case12 => e.subst.mergeIdx < n.numDiv
  | .case2 => True

def StepRel (n : StepData M) (e : Edge M) : Prop :=
  StepApplicable n e ∧
    rootLedger e.child = stepUpdate n e.case e.subst
```

Typed `Fin` is stronger, but not a small field change: the present `Edge M` and `ChartSubst M` do not depend on parent `n`. A proper design would require parent-indexed, case-specific edges/substitutions. Case 2 must not carry `Fin n.numDiv`, since it can legitimately run when `numDiv = 0`.

There is no mathematical downside for the constructor—it already knows the target—but there is engineering churn from dependent types, transports, and changed tree traversals. Recommendation: add the guard now; adopt typed `Fin` during a planned carrier redesign.

### Q3

**FACT:** Confirmed. `RootLedger` equality enforces all four fields. Once `numDiv` agrees, equality of `divExp` and `divTilde` is pointwise after the dependent transport; `cleared` must also agree.

Thus a child with the same positive `numDiv` but a wrong exponent at any index cannot satisfy `StepRel`. Only syntactically different but extensionally equal functions can. For `numDiv = 0`, there is no observable exponent entry to corrupt.

Fields outside `RootLedger`, including `support`, can still differ.

### Q4

There is another likely blocker.

**FACT:** Case 2 sets `cleared := n.cleared + n.resRows` in [EngineObligations.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev2/lean/DLNFibre/DLN/RLCT/Engine/EngineObligations.lean:119). The extracted preprint says the case‑2 transition produces one pivot and continues “with `J` increased by one” [aoyagi-2023-extracted-text.txt](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev2/theory/aoyagi-2023-reproduction/aoyagi-2023-extracted-text.txt:1499).

**INFER:** Since the update appends exactly one divisor, case 2 should also use `cleared + 1`. A macro-step clearing the whole residual would require additional justification and likely multiple appended divisors. The current formula agrees only when `resRows = 1`.

Other fidelity omissions remain:

- `runLen` and case applicability are not tied to an actual positive partial equal run or the selected divisor.
- `resRows`/`resCols` are not constrained to the claimed residual dimensions.
- `StepRel` does not certify `layer`, `bExp`, `support`, `localSub`, or `jacPow`.

**FACT:** Given the established driver dependency, the deliberate support omission has no additional finiteness impact. It does mean `StepRel` certifies only the ledger core, not the full Aoyagi transition.