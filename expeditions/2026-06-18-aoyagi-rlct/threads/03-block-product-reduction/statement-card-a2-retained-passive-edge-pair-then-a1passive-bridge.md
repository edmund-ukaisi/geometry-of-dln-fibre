# Statement card: A2 retained-passive edge-pair then `A1passive` bridge

## Claim

The target edge-pair raw-tuple shear composed with the post-edge-pair
`A1passive` shear has absolute determinant one and normalises exactly the
`A1passive`, `(F2,C)`, and `A3passive` components of the actual raw-order
Frechet derivative to the point-specialized formal raw-order Jacobian.

This is a componentwise bridge only.  It does not assert full raw-tuple
agreement.

## Lean Surface

```text
retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveShear_fderiv_A1passive_eq_formalRawOrderJacobianAt
retainedPassiveTargetEdgePairThenA1passiveShear_fderiv_F2C_eq_formalRawOrderJacobianAt
retainedPassiveTargetEdgePairThenA1passiveShear_fderiv_A3passive_eq_formalRawOrderJacobianAt
```

Private helper:

```text
retainedPassiveF2SuccessorFamilyLinearMap_formalRawF2CLinearEquivAt_symm_targetEdgePairShearAt
```

## Dependencies

- `retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_abs_det_eq_one`;
- `retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_abs_det_eq_one`;
- `retainedPassiveFormalRawF2CLinearEquivAt_symm_targetEdgePairShearAt_fst`;
- `retainedPassiveTargetEdgePairShearAt_fderiv_eq_formalF2C`;
- `A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `rawEdgeTupleA3_fderiv_topologyTupleEdgeRawOrder_castSucc_eq_formalRawOrderJacobianAt`.

## Lean Status

Proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.
Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`
passed.

## Nonclaims

This is not the full target normaliser.  It does not prove agreement for
`Ctop` or `F3`, does not feed the conditional determinant bridge, and does not
prove actual Frechet determinant equality, source-prior transport, normal
crossings, pole order, or RLCT.
