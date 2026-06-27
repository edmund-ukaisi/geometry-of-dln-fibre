# Statement Card - A2 retained-passive all-edge pair source-staged target shear

Status: reproduced; Lean proved; focused/full builds passed; xhigh review
passed.

## Claim

For a retained-passive tuple `z` in the determinant chart and tangent `v`,
define the staged successor source `F2` family over retained edges by

```text
Xsucc =
  Fin.snoc
    (fun p : Fin M =>
      cast_{p.succ.castSucc = p.castSucc.succ}(v.F2_(p.succ)))
    0.
```

Then the all-edge normalized actual target-side pair

```text
U_F(q) =
  Dzv.F2_q
  + rawEdgeTupleA1(Dzv)_q * coord.F2 q.castSucc
  - Xsucc(q) * coord.C q,

U_C(q) =
  Dzv.C_q
  + rawEdgeTupleA3(Dzv)_q * coord.F2 q.castSucc
```

agrees as a pair of edge families with the `(F2,C)` component of the
point-specialized formal raw-order output.  Consequently the already-proved
formal edge-pair inverse recovers the full source `(F2,C)` family from
`(U_F,U_C)`.

## Lean Target

Expected Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Expected Lean names:

```text
retainedPassiveSourceStagedSuccessorF2
F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_sourcePair
```

Component recovery wrappers may be added only if they simplify downstream use.

## Dependencies

- `F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassiveFormalRawF2CLinearEquivAt_symm_recovers_sourcePair`;
- `Fin.snoc_castSucc`, `Fin.snoc_last`, and `Fin.lastCases`.

## Review Plan

Read-only xhigh review passed.  The review checked:

- whether terminal zero is used only at `Fin.last M`;
- whether nonterminal successor tangents use the source tangent with the
  dependent cast;
- whether the theorem remains only an edge-family packaging lemma;
- whether the docs and Lean statements have the same staged family.

## Kill Conditions

- The theorem must not set every successor tangent to zero.
- The theorem must not omit the dependent cast in the nonterminal branch.
- The theorem must not claim determinant equality, determinant-one target
  shear, a target-side `LinearEquiv`, descending induction, measure transport,
  normal crossings, pole order, or RLCT.

## Nonclaims

No full descending construction, no actual derivative determinant comparison,
no retained-passive measure theorem, no normal-crossing theorem, no pole order,
and no RLCT follows from this all-edge source-staged package.
