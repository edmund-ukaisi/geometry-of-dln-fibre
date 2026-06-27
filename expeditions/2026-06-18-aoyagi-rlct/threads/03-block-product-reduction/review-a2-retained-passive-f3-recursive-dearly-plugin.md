# Review - A2 retained-passive F3 recursive dEarly plug-in

Reviewer: xhigh `Franklin the 2nd`.

Verdict: PASS.  No findings.

## Scope

Reviewed the two new Lean theorems in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

The reviewer did a read-only audit after the controller had verified the
focused Jacobian build and the full `DLNFibre` build.

## Findings

No findings.

Checked points:

- The statement uses `z : RetainedPassiveRawTopologyTuple (M := M+1)` and
  correctly instantiates the older positive-tail bridge with `(M := M+1)`.
- For `qLast : Fin (M+1) := Fin.last M`, the proof
  `qLast.succ = Fin.last (M+1)` by `rfl` is sound.
- `p0` and `Earlyfun` align with the `m = 0` instance of
  `fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply`.
- The recovery theorem uses right multiplication by
  `(-(coord.solvedA1 (Fin.last (M+1))))^-1`, matching the formal `F3` output
  and the existing recovery lemma.
- The proof only rewrites `(fderiv ℝ Earlyfun z) v = dEarly`; it does not
  commute matrix factors.
- The names and docstrings state component equality/recovery only and make no
  determinant or RLCT claim.

## Review command note

The reviewer did not rerun Lean.  Controller verification separately used the
worktree `scripts/lb` focused Jacobian build, the full `DLNFibre` build,
`scripts/sorries`, `git diff --check`, forbidden-marker search on the touched
file, and direct `#print axioms` audits.
