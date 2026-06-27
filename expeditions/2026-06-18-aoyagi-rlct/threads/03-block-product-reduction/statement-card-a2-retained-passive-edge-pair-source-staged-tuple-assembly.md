# Statement Card - A2 retained-passive edge-pair source-staged tuple assembly

Status: reproduced; Lean proved; focused/full builds passed; xhigh review
passed.

## Claim

For a retained-passive tuple `z` in the determinant chart and tangent `v`, the
hybrid tuple that keeps the existing derivative-staged `A1passive`, passive
`A3`, `Ctop`, and `F3` entries but replaces the `(F2,C)` edge-family entries
by the all-edge source-staged normalized family agrees with the
point-specialized formal raw-order Jacobian.

Only the `(F2,C)` branch is source-staged.  The source-staged successor family
is `retainedPassiveSourceStagedSuccessorF2 v`.

## Lean Target

Expected Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Expected Lean names:

```text
edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt
edgePairSourceStaged_sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

## Dependencies

- `shearedTopologyTupleEdgeRawOrderFDerivAt`;
- `sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassiveSourceStagedSuccessorF2`;
- `F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- product extensionality for the nested retained-passive raw tuple.

## Review

Xhigh read-only review passed.  The review checked:

- the theorem being a hybrid whole-tuple package only;
- `A1passive`, `Ctop`, and `F3` remaining derivative-staged;
- `Xsucc` remaining source tangent data, not target-recovered data;
- no determinant, target-side `LinearEquiv`, measure, normal-crossing,
  pole-order, or RLCT claim.

## Nonclaims

No target-side `LinearEquiv`, determinant-one shear, actual derivative
determinant formula, measure transport, normal crossings, pole order, or RLCT
is proved by this tuple package.
