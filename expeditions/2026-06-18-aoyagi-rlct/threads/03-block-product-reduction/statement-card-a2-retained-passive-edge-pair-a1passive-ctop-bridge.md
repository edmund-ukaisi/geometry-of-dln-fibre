# Statement card: A2 retained-passive edge-pair, `A1passive`, and `Ctop` bridge

## Claim

The target edge-pair raw-tuple shear, the post-edge-pair `A1passive` shear,
and the post-`A1passive` `Ctop` shear compose to a raw-tuple linear
equivalence with absolute determinant one.  On actual raw-order Frechet
derivative targets, the composed map normalises the `Ctop` component to the
point-specialized formal raw-order Jacobian.

This is still a componentwise bridge only.  It does not assert full raw-tuple
agreement.

## Lean Surface

```text
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt_apply
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt_det_eq_one
retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopShear_fderiv_Ctop_eq_formalRawOrderJacobianAt
```

Private helpers:

```text
retainedPassiveRawCtopFocusLinearEquiv
retainedPassivePostA1passiveTailFDerivLinearMapAt
retainedPassivePostA1passiveTailFDerivLinearMapAt_fderiv_after_T12_eq_targetStaged
retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt_Ctop
retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt_F2C
rawEdgeTupleA3_retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt
```

## Dependencies

- `retainedPassiveTargetEdgePairThenA1passiveShearRawTupleLinearEquivAt_abs_det_eq_one`;
- `retainedPassivePostA1passiveCtopShearRawTupleLinearEquivAt_abs_det_eq_one`;
- `Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `retainedPassivePostA1passiveTailFDerivLinearMapAt_fderiv_after_T12_eq_targetStaged`;
- `retainedPassiveF2SuccessorFamilyLinearMap_formalRawF2CLinearEquivAt_symm_targetEdgePairShearAt`;
- preservation of `Ctop`, `(F2,C)`, and `rawEdgeTupleA3` by the first two
  target-side stages where appropriate.

## Lean Status

Proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.
Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`
passed.

## Nonclaims

This is not the full target normaliser.  It does not prove agreement for
`F3`, full raw-tuple equality, actual raw-order Frechet determinant equality,
source-prior transport, normal crossings, pole order, or RLCT.  The `Ctop`
coordinate is the target-staged coordinate itself, not the `Tail`-multiplied
source recovery expression.
