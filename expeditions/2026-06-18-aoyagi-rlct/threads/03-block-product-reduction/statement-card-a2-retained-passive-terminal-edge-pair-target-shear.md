# Statement Card - A2 retained-passive terminal edge-pair target shear

Status: reproduced, Lean-proved, and xhigh-reviewed.

## Claim

At the terminal retained-passive edge `p = Fin.last M`, the normalized actual
target-side pair

```text
U_F = Dzv.F2_p + rawEdgeTupleA1(Dzv)_p * coord.F2 p.castSucc,
U_C = Dzv.C_p  + rawEdgeTupleA3(Dzv)_p * coord.F2 p.castSucc
```

equals the point-specialized formal `(F2,C)` output pair.  Consequently the
formal inverse formulas recover the source terminal `F2` and `C` tangent
components from `(U_F,U_C)`.

## Lean Target

Expected Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Expected Lean names:

```text
F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C
```

## Dependencies

- `F2_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_F2`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_C`.

## Kill Conditions

- If this is generalized to all edges without a descending construction, it
  overclaims.
- If the inverse uses `Tail` or `LastTop`, the edge-local recovery is wrong.
- If the statement asserts determinant equality or a determinant-one target
  shear, it exceeds the proved content.

## Nonclaims

No nonterminal staged target-side shear, no full retained-passive determinant
factorization, no measure theorem, no normal crossings, no pole order, and no
RLCT follows from this terminal edge-pair target package.
