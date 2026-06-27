# Review - A2 retained-passive recursive A1-tail Ctop plug-in

Reviewer: xhigh `Dirac the 2nd`.

Verdict: PASS.  No findings.

## Scope

Reviewed the new Lean slice in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveTargetStagedA1passiveTangentAt
retainedPassiveTargetStagedA1passiveTangentAt_fderiv_eq_source
retainedPassiveA1TailTargetStagedFDerivAt
retainedPassiveA1TailTargetStagedFDerivAt_self
retainedPassiveA1TailTargetStagedFDerivAt_step
retainedPassiveA1TailTargetStagedFDerivAt_zero
retainedPassiveA1seedTailProductAt
fderiv_retainedPassive_A1seed_residualFactorProduct_targetStaged_apply
fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

The reviewer performed a read-only mathematical and Lean-shape audit of the
uncommitted branch state.  Controller verification separately ran the focused
and full builds and the hygiene gates.

## Findings

No findings.

Checked points:

- The target-only definitions use only `z`, a target tuple `w`,
  target-recovered successor `F2`, and raw target `A3`; no source tangent is
  baked into the claimed target-only API.
- The tail recursion indexing/order matches the residual-factor product:
  derivative successor term on the left, current `A1seed (m+1)` appended on
  the right.
- The boundary `m = M` is the empty suffix derivative `0`; `M = 0` is covered
  by the same path.
- The `Ctop` bridge/recovery only proves that the staged expression equals the
  formal Jacobian branch and recovers source `Ctop` after multiplying by
  `Tail`; it does not assert a determinant-one normalizer or RLCT consequence.
- The reviewed file contained no `sorry`, `axiom`, `native_decide`, `#exit`,
  `unsafe`, `implemented_by`, `extern`, or `admit`; `git diff --check` was
  clean.

## Controller Verification

After the review, the controller ran:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
scripts/sorries
git diff --check
rg -n "sorry|axiom|native_decide|#exit" lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

The focused Jacobian build and full `DLNFibre` build passed.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and the marker
search was clean.  Direct `#print axioms` audits for

```text
fderiv_retainedPassive_A1seed_residualFactorProduct_targetStaged_apply
fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

reported only `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

This review does not certify the whole-tuple target-side normalizer,
determinant one, determinant equality, source-prior transport,
inverse-density pushforward, normal crossings, pole order, or RLCT.
