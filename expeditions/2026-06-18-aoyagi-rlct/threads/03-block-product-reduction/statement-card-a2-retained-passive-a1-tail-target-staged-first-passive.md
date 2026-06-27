# Statement Card - A2 retained-passive A1-tail first passive target staging

Status: Lean proved; xhigh independent review passed.

## Claim

For positive retained-passive tail length, target-stage only the first passive
`A1` source tangent in the derivative of the passive top-left suffix.  With

```text
q = <0, hM> : Fin M,
p = q.succ  : Fin (M+1),
```

and `Psucc` the residual product starting at `p.succ`,

```text
(fderiv Tfun z) v =
  (fderiv Psucc z) v * data.A1seed p
  + Psucc(z) * targetA1(q),
```

where

```text
targetA1(q) =
  Dzv.A1passive(q)
  - XsuccF2(q.succ) * coord.solvedA3(q.succ)
  - coord.F2(q.succ.succ) * rawEdgeTupleA3(Dzv, q.succ).
```

The residual derivative `(fderiv Psucc z) v` remains explicit.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean names:

```text
fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_target_staged_apply
fderiv_retainedPassive_A1TailAfterFirst_pos_target_staged_apply
Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop
```

## Dependencies

- `fderiv_retainedPassive_A1TailAfterFirst_pos_apply`;
- `A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive`;
- `Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.

## Cited

None.

## Deferred

Expansion of `(fderiv Psucc z) v`; terminal cleanup; full recursive passive
suffix staging; full `Ctop`/`F3` target staging; determinant equality; measure
transport; normal crossings; pole order; RLCT.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed after the Lean
theorems were added.  The independent xhigh review passed in
`review-a2-retained-passive-a1-tail-target-staged-first-passive.md`.

## Kill Conditions

- The theorem must require `0 < M`.
- The passive `A1` target replacement must use `q.succ`, not the separate Ctop
  edge index.
- Matrix factor order must remain
  `Tail^-1 * (...) * Tail^-1 * coord.Ctop` in the Ctop consumer.
- The theorem must not simplify the `M = 1` empty-suffix case unless that is
  proved separately.
