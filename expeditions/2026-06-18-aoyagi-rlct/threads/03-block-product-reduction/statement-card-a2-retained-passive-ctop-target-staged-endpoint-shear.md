# Statement Card - A2 retained-passive Ctop target-staged endpoint shear

Status: reproduced; Lean proved; focused/full builds passed; sorry,
whitespace, and axiom audits passed; independent xhigh checker passed.

## Claim

For a retained-passive tuple `z` in the determinant chart and tangent `v`, let
`Dzv = d(topologyTupleEdgeRawOrder)_z(v)`.  The existing zero/positive Ctop
endpoint formulas can be rewritten with target-side successor data:

```text
Dzv.Ctop
  - targetXsuccF2(0) * coord.solvedA3(0)
  - coord.F2(0.succ) * rawEdgeTupleA3(Dzv,0)
  + explicit_tail_term
= formal.Ctop.
```

For `M = 0`, `explicit_tail_term = 0`.  For `0 < M`, the explicit tail term is
the already-landed first passive suffix-product derivative expression:

```text
Tail^{-1} *
  (d(Psucc)_z(v) * A1seed_z(p) + Psucc(z) * v.A1passive_q) *
  Tail^{-1} * coord.Ctop.
```

Here `targetXsuccF2` is
`retainedPassiveTargetRecoveredSuccessorF2At z Dzv`, and
`rawEdgeTupleA3(Dzv,0)` is used only under multiplication by
`coord.F2(0.succ)`.

Consequently, after multiplying the same expression by `Tail` on the left, it
recovers the source `Ctop` tangent.

## Lean Target

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean names:

```text
Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

## Assumed

The Lean theorems should assume

```text
z in topologyTupleDetChartSet.
```

The positive-tail theorems additionally assume `0 < M`.

## Dependencies

- `retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2`;
- `retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3`;
- `Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop`.

## Review

Independent xhigh checker passed.  Review artifact:

```text
review-a2-retained-passive-ctop-target-staged-endpoint-shear.md
```

Controller verification:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre
scripts/sorries
git diff --check
#print axioms for the four theorem names above
```

The builds and audits passed.  The axiom audit reported only
`[propext, Classical.choice, Quot.sound]`.

## Cited

None.

## Deferred

`F3` target staging; whole-tuple target-side normalization; determinant-one
target-side `LinearEquiv`; actual derivative determinant equality; measure
transport; normal crossings; pole order; RLCT.

## Kill Conditions

- The terminal raw lower-left target derivative must not be identified with
  source-staged zero before multiplication by the terminal zero extended `F2`
  slot.
- The successor `F2` correction must be the target-recovered family, not the
  already-landed source-staged family.
- The positive-tail expression must preserve the noncommutative order of the
  suffix derivative term.
- The theorem must not claim determinant equality, determinant-one target
  shear, measure transport, normal crossings, pole order, or RLCT.
