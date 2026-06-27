# Statement Card - A2 retained-passive Ctop two-positive-tail second A1 target staging

Status: Lean proved; xhigh independent review passed.

## Claim

For retained-passive tail length `(M+1)+1`, expand the remaining suffix
derivative in the first-passive target-staged `Ctop` bridge by one passive
`A1` product-rule step, and target-stage the second passive `A1` tangent.

With

```text
q0 = 0 : Fin ((M+1)+1),
q1 = (0 : Fin (M+1)).succ : Fin ((M+1)+1),
p0 = q0.succ,
p1 = q1.succ,
```

and suffixes

```text
Psucc  starts at p0.succ = p1.castSucc,
Psucc1 starts at p1.succ,
```

the substitution is

```text
(fderiv Psucc z) v =
  (fderiv Psucc1 z) v * data.A1seed p1
  + Psucc1(z) * targetA1(q1).
```

In the `Ctop` bridge this yields

```text
Tail^-1 *
  (((fderiv Psucc1 z) v * data.A1seed p1
      + Psucc1(z) * targetA1(q1))
    * data.A1seed p0
    + Psucc(z) * targetA1(q0))
  * Tail^-1 * coord.Ctop.
```

The residual derivative `(fderiv Psucc1 z) v` remains explicit.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean names:

```text
Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

## Dependencies

- `Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_target_staged_apply`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop`.

## Cited

None.

## Deferred

Expansion of `(fderiv Psucc1 z) v`; terminal/empty-suffix cleanup; full
recursive passive suffix staging; full `Ctop` or `F3` target staging;
determinant equality; measure transport; normal crossings; pole order; RLCT.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.  The full
`DLNFibre` build passed with only pre-existing style warnings.  `scripts/sorries`
reported zero forbidden markers, `git diff --check` was clean, the two theorem
axiom audits reported only `[propext, Classical.choice, Quot.sound]`, and
xhigh independent review passed in
`review-a2-retained-passive-ctop-two-positive-tail-second-a1-target-staging.md`.

## Kill Conditions

- The theorem must require at least two passive tail factors by using tail
  length `(M+1)+1`.
- The second passive `A1` target replacement must use `q1`, not the F3
  successor theorem's `castSucc` source tangent pattern.
- Matrix factor order must remain
  `Tail^-1 * (...) * Tail^-1 * coord.Ctop`.
- The theorem must not simplify the `M=0` terminal second-stage suffix unless
  separately proved.
