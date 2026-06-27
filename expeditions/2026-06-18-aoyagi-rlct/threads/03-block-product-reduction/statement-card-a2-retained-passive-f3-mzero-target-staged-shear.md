# Statement Card - A2 retained-passive F3 zero-tail target-staged shear

Status: reproduced; Lean proved; focused/full builds passed; sorry,
whitespace, and axiom audits passed; independent xhigh checker passed.

## Claim

For a retained-passive tuple `z` with `M = 0` in the determinant chart and
tangent `v`, let

```text
Dzv = d(topologyTupleEdgeRawOrder)_z(v),
targetXsuccF2 = retainedPassiveTargetRecoveredSuccessorF2At z Dzv.
```

Define the one-edge target-staged Ctop expression

```text
targetCtop =
  Dzv.Ctop
    - targetXsuccF2(0) * coord.solvedA3(0)
    - coord.F2(0.succ) * rawEdgeTupleA3(Dzv,0).
```

Then the terminal `F3` bridge can be rewritten as

```text
Dzv.F3 + coord.F3 * targetCtop = formal.F3.
```

Consequently,

```text
(Dzv.F3 + coord.F3 * targetCtop) * (-(coord.Ctop))^{-1} = v.F3.
```

## Lean target

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Proposed Lean names:

```text
F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

## Assumed

The Lean theorems assume

```text
z in topologyTupleDetChartSet.
```

## Dependencies

- `F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_F3`;
- simplification of the one-edge `Early` tail to zero;
- simplification of the one-edge terminal top product to `coord.Ctop`.

## Review

Independent xhigh implementation reviewer `Bernoulli` passed.  Review
artifact:

```text
review-a2-retained-passive-f3-mzero-target-staged-shear.md
```

Controller verification:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre
scripts/sorries
git diff --check
#print axioms for the two theorem names above
```

The focused and full builds passed.  The sorry audit reported zero forbidden
markers.  `git diff --check` passed.  The new theorem axiom audits report only
`[propext, Classical.choice, Quot.sound]`.

## Cited

None.

## Deferred

Positive-tail `F3` target staging; the derivative recurrence for `Early`;
whole-tuple target-side normalization; determinant-one target-side
`LinearEquiv`; actual derivative determinant equality; measure transport;
normal crossings; pole order; RLCT.

## Kill conditions

- The terminal raw lower-left target derivative must not be identified with
  zero outside the terminal zero extended `F2` multiplier.
- The right recovery factor is `(-(coord.Ctop))^{-1}` in the one-edge case,
  not the passive Ctop recovery tail.
- The theorem must not contain source tangents in the advertised target-staged
  expression.
- The theorem must not claim determinant equality, determinant-one target
  shear, measure transport, normal crossings, pole order, or RLCT.
