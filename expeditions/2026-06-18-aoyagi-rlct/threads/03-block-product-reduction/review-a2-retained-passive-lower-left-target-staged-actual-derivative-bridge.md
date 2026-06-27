# Review - A2 retained-passive lower-left target-staged actual derivative bridge

Reviewer: xhigh `Erdos the 2nd`.

Verdict: PASS.  No findings.

## Scope

Reviewed the new Lean theorem:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply
```

and the local uncommitted diff in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`.

## Findings

No findings.

Checked points:

- The type-level shift `κ' : Fin ((M+1)+2)` is consistent with the staged
  target definition and the one-step recurrences.
- The actual lower-left tail sum uses the widened bound `m ≤ M+2`, while the
  staged target expression remains indexed by `m ≤ M+1`.
- The recursive base is the zeroed-final tail at `m = M+1`.
- The zero branch uses the solved top-left tangent.
- Successor branches use `v.1 s.castSucc`.
- The induction `congrArg` steps substitute only the recursive successor
  derivative into the same step-core context; no proof-irrelevance or
  `simpa` issue was found beyond harmless proof normalization.

## Review command note

The reviewer reported checking with:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Controller verification separately used the worktree `scripts/lb` build path,
the full `DLNFibre` build, `scripts/sorries`, `git diff --check`, forbidden
marker search, and a direct axiom audit.
