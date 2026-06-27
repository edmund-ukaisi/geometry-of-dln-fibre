# Statement Card - A2 retained-passive target edge-pair recovery

Status: reproduced; Lean proved; focused/full builds passed; xhigh review
passed after documentation status repair.

## Claim

For a retained-passive tuple `z` in the determinant chart and a target raw tuple
`w`, define a backward recovered `F2` family by descending over retained edges.
The terminal edge uses zero successor correction.  A nonterminal edge uses the
already recovered successor `F2` tangent, transported by the dependent equality
`p.succ.castSucc = p.castSucc.succ`.

When `w = d(topologyTupleEdgeRawOrder)_z(v)`, the recovered target-side `F2`
family equals the source `F2` tangent family:

```text
Frec(q) = v.F2_q.
```

Consequently the target-side normalized edge pair

```text
U_F(q) =
  Dzv.F2_q
  + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
  - targetXsucc(q) * coord.C q,

U_C(q) =
  Dzv.C_q
  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc
```

agrees with the `(F2,C)` component of the point-specialized formal raw-order
output.  Applying the formal edge-pair inverse then recovers `(v.F2, v.C)`.

## Lean Target

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean names:

```text
retainedPassiveTargetRecoveredF2At
retainedPassiveTargetRecoveredSuccessorF2At
retainedPassiveTargetRecoveredF2At_fderiv_eq_sourceF2
retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2
retainedPassiveTargetEdgePairShearAt
retainedPassiveTargetEdgePairShearAt_fderiv_eq_formalF2C
retainedPassiveTargetEdgePairShearAt_fderiv_recovers_sourcePair
```

## Dependencies

- `F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2`;
- `F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2`;
- `F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassiveFormalRawF2CLinearEquivAt_symm_recovers_sourcePair`;
- `Fin.reverseInduction`, `Fin.snoc`, and the cast `Fin.succ_castSucc`.

## Assumed

The Lean theorems assume

```text
z in topologyTupleDetChartSet.
```

This is used to invert each `coord.solvedA1 q` through the existing formal
edge-pair recovery theorems.

## Cited

None.

## Deferred

Packaging the target-side shear as a determinant-one `LinearEquiv`; proving
actual derivative determinant equality; measure transport; normal crossings;
pole order; RLCT extraction.

## Review Plan

Independent xhigh review passed after status-wording repair.  The review
checked the terminal zero convention, the nonterminal cast direction, the
downward recurrence, the determinant-chart hypothesis, and the nonclaim
boundary.

Review artifact:

```text
review-a2-retained-passive-target-edge-pair-recovery.md
```

## Kill Conditions

- The terminal branch must not use a nonzero successor correction.
- The nonterminal branch must not use zero or a source tangent directly; it
  must use the recovered target-side successor.
- The theorem must not claim determinant equality, a determinant-one
  `LinearEquiv`, measure transport, normal crossings, pole order, or RLCT.
