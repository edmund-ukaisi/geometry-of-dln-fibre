# Statement Card - A2 retained-passive F3 three-positive-tail next-next successor substitution

Status: proved in Lean; reproduction written; independent xhigh reviews passed.

## Claim

For tail length `((M+1)+1)+1`, consume the successor-index retained-passive
`dEarly` theorem in the remaining `NextNextfun` derivative of the
two-positive-tail `F3` bridge.

The inherited two-positive indices are

```text
q0 = 0,
p0 = q0.castSucc,
r0 = q0.succ,
s0 = 0 : Fin ((M+1)+1),
q1 = s0.succ,
u1 = s0.castSucc,
p1 = q1.castSucc,
r1 = q1.succ.
```

The new second-successor indices are

```text
t0 = 0 : Fin (M+1),
s1 = t0.succ : Fin ((M+1)+1),
q2 = s1.succ,
u2 = s1.castSucc,
p2 = q2.castSucc,
r2 = q2.succ.
```

The intended replacement is

```text
(fderiv NextNextfun z) v =
  -(((fderiv Cnext2 z) v * data.C r2 + Cnext2 z * v.C r2)
      * A3p2 z * (Pcast2 z)^-1)
  - (Cprod2 z * dG2 * (Pcast2 z)^-1)
  + Cprod2 z * A3p2 z * (Pcast2 z)^-1
      * (dPsucc2 * coord.solvedA1 p2 + Psucc2 z * v.1 u2)
      * (Pcast2 z)^-1
  + (fderiv NextNextNextfun z) v.
```

Substitute this only into the final summand of `dNext1`; leave the terminal
`dLast` target-staged factor unchanged.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean names:

```text
F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3
```

Both names are proved in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

## Dependencies

- `F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_F3`.

## Cited

None.

## Deferred

Expansion of `dPsucc`, `dPsucc1`, `dPsucc2`, and the next recursive derivative;
terminal cleanup; full recursive expansion of `dEarly`; full positive-tail
`F3` target staging; determinant equality; measure transport; normal crossings;
pole order; RLCT.

## Verification Plan

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed, and the full
`DLNFibre` build passed with only pre-existing style warnings.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, and the axiom
audit for both new theorem names reported only
`[propext, Classical.choice, Quot.sound]`.  Xhigh pre-Lean indexing review and
post-Lean fidelity review passed in
`review-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md`.

## Kill Conditions

- The theorem must not cover the one- or two-positive-tail cases.
- The second successor tangent must be `v.1 u2`, not `v.1 q2`.
- The factor order must remain
  `Cprod2 * A3p2 * Pcast2^-1 * (...) * Pcast2^-1`.
- The outer product
  `- dEarly_expanded_two_successor_steps * terminalSolvedA1`
  must not be distributed or commuted.
