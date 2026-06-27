# Statement Card - A2 retained-passive F3 two-positive-tail next-successor substitution

Status: Lean proved; focused/full builds and audits passed; xhigh review passed.

## Claim

For tail length `(M+1)+1`, consume the successor-index retained-passive
`dEarly` theorem in the remaining `Next0` derivative of the positive-tail
`F3` bridge.

The first expansion uses

```text
q0 = 0                 : Fin ((M+1)+1),
p0 = q0.castSucc       : Fin (((M+1)+1)+1),
r0 = q0.succ           : Fin (((M+1)+1)+1).
```

The recursive successor substitution uses

```text
s0 = 0                 : Fin (M+1),
q1 = s0.succ           : Fin ((M+1)+1),
u1 = s0.castSucc       : Fin ((M+1)+1),
p1 = q1.castSucc       : Fin (((M+1)+1)+1),
r1 = q1.succ           : Fin (((M+1)+1)+1).
```

The intended replacement is

```text
(fderiv Next0 z) v =
  -(((fderiv Cnext1 z) v * data.C r1 + Cnext1 z * v.C r1)
      * A3p1 z * (Pcast1 z)^-1)
  - (Cprod1 z * dG1 * (Pcast1 z)^-1)
  + Cprod1 z * A3p1 z * (Pcast1 z)^-1
      * (dPsucc1 * coord.solvedA1 p1 + Psucc1 z * v.1 u1)
      * (Pcast1 z)^-1
  + (fderiv Next1 z) v.
```

Substitute this only into the final summand of the first expanded `dEarly`;
the terminal `dLast` target-staged factor remains unchanged.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean name:

```text
F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

## Verification

Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`; full `DLNFibre`
build passed with only pre-existing unrelated style warnings.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and the theorem
axiom audit reported only `[propext, Classical.choice, Quot.sound]`.
Independent review passed in
`review-a2-retained-passive-f3-two-positive-tail-next-succ-substitution.md`.

## Dependencies

- `F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply`;
- `Fin.succ_castSucc` through the successor theorem.

## Cited

None.

## Deferred

Expansion of `dPsucc1`; terminal cleanup; full recursive expansion of
`dEarly`; full positive-tail `F3` target staging; determinant equality;
measure transport; normal crossings; pole order; RLCT.

## Kill Conditions

- The theorem must not cover the one-positive-tail case.
- The successor tangent must be `v.1 u1`, not `v.1 q1`.
- The factor order must remain
  `Cprod1 * A3p1 * Pcast1^-1 * (...) * Pcast1^-1`.
- The outer product
  `- dEarly_expanded_once_more * coord.solvedA1(Fin.last ((M+1)+1))`
  must not be distributed or commuted.
