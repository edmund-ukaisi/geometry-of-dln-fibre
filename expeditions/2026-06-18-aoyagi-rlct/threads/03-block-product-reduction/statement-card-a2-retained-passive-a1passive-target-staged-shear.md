# Statement Card - A2 retained-passive passive A1 target-staged shear

Status: reproduced; Lean proved; focused/full builds passed; sorry,
whitespace, and axiom audits passed; xhigh review passed.

## Claim

For a retained-passive tuple `z` in the determinant chart and tangent `v`, let
`Dzv = d(topologyTupleEdgeRawOrder)_z(v)`.  The passive top-left correction
can be written with target-side data:

```text
Dzv.A1passive_p
  - targetXsuccF2(p.succ) * coord.solvedA3(p.succ)
  - coord.F2(p.succ.succ) * rawEdgeTupleA3(Dzv,p.succ)
= formal.A1passive_p.
```

Here `targetXsuccF2` is the target-recovered successor `F2` family from
`retainedPassiveTargetRecoveredSuccessorF2At`.  The lower-left target readout
`rawEdgeTupleA3(Dzv,p.succ)` is used only under multiplication by the extended
successor `F2` slot, which kills the terminal case.

Consequently the same expression recovers the source passive `A1` tangent:

```text
... = v.A1passive_p.
```

## Lean Target

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean names:

```text
retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3
A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive
```

## Assumed

The Lean theorems assume

```text
z in topologyTupleDetChartSet.
```

This is needed by the existing derivative/formal bridges and target-recovered
successor `F2` theorem.

## Dependencies

- `retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2`;
- `retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3`;
- `A1passive_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_A1passive`.

## Review

Independent xhigh review passed.  Review artifact:

```text
review-a2-retained-passive-a1passive-target-staged-shear.md
```

Controller verification:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre
scripts/sorries
git diff --check
#print axioms for the three theorem names above
```

The builds and audits passed.  The axiom audit reported only
`[propext, Classical.choice, Quot.sound]`.

## Cited

None.

## Deferred

`Ctop` target staging; `F3` target staging; whole-tuple target-side
normalization; determinant-one target-side `LinearEquiv`; actual derivative
determinant equality; measure transport; normal crossings; pole order; RLCT.

## Kill Conditions

- The terminal raw lower-left derivative must not be identified with zero
  before multiplication by the terminal zero extended `F2` slot.
- The successor `F2` correction must be the target-recovered family, not the
  already-landed source-staged family.
- The theorem must not claim determinant equality, determinant-one target
  shear, measure transport, normal crossings, pole order, or RLCT.
