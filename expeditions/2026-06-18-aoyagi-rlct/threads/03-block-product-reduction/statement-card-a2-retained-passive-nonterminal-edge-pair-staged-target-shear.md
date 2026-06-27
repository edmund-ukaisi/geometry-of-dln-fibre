# Statement Card - A2 retained-passive nonterminal edge-pair staged target shear

Status: reproduced; Lean proved; focused/full builds passed; xhigh re-review
passed after repair.

## Claim

For a nonterminal retained edge `q = p.castSucc` with `p : Fin M`, the
normalized actual target-side pair

```text
U_F =
  Dzv.F2_q
  + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
  - X_succ * coord.C q,

U_C =
  Dzv.C_q
  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc
```

agrees with the point-specialized formal `(F2,C)` output pair when the staged
successor input is the successor source tangent transported to the extended
slot:

```text
X_succ =
  cast_{p.succ.castSucc = p.castSucc.succ}(v.F2_(p.succ)).
```

Consequently the formal inverse formulas recover the current source `F2` and
`C` tangent components from `(U_F,U_C)`.

## Lean Target

Expected Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Expected Lean names:

```text
fderiv_retainedPassive_toCoordinateData_F2_nonterminal_succ_apply
F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C
```

The derivative-staged bridge used internally is:

```text
F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2
F2C_nonterminal_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C
```

## Dependencies

- `F2_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_F2`;
- `retainedPassiveFormalRawOrderJacobianAt_recovers_C`;
- the projection derivative of the nonterminal extended `F2` slot.

## Review

`review-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`
records the first xhigh FAIL on the derivative/source-staging mismatch and the
post-repair xhigh PASS.

## Kill Conditions

- If the theorem kills the successor term for nonterminal edges, it is wrong.
- If the theorem omits the dependent-index cast between `p.succ.castSucc` and
  `p.castSucc.succ`, it is not a well-scoped Lean statement.
- If the theorem uses `p.succ = Fin.last (M+1)` for `p : Fin M`, it has
  confused the successor retained edge with the terminal extended zero slot.
- If the theorem asserts determinant equality or a determinant-one target
  shear, it exceeds the one-step result.

## Nonclaims

No full descending induction, no retained-passive determinant factorization,
no measure theorem, no normal crossings, no pole order, and no RLCT follows
from this staged one-step target package.
