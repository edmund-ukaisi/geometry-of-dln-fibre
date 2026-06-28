# Statement card: A2 retained-passive post-`Ctop` `F3` zero-tail shear

## Claim

In the single-edge retained-passive case (`M = 0`), after the edge-pair,
post-edge-pair `A1passive`, and post-`A1passive` `Ctop` stages, the terminal
`F3` target coordinate is obtained by a raw-tuple shear changing only the final
`F3` field:

```text
F3 |-> F3 + coord.F3 * Ctop.
```

This shear has determinant one.  Composed with the first three target-side
stages, it has absolute determinant one and sends the actual raw-order
derivative's `F3` component to the point-specialized formal raw-order Jacobian
in the zero-tail case.

## Lean Surface

```text
retainedPassivePostCtopF3ZeroShearRawTupleLinearEquivAt
retainedPassivePostCtopF3ZeroShearRawTupleLinearEquivAt_apply
retainedPassivePostCtopF3ZeroShearRawTupleLinearEquivAt_det_eq_one
retainedPassivePostCtopF3ZeroShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShear_fderiv_F3_eq_formalRawOrderJacobianAt
```

Private helpers include the reusable `F3`-focus regrouping
`retainedPassiveRawF3FocusLinearEquiv`.

## Dependencies

- the composed edge-pair, `A1passive`, and `Ctop` raw-tuple equivalence and
  absolute determinant theorem;
- `Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- `F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`;
- preservation of the `F3` field by the first three target-side stages.

## Lean Status

Proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.
Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`
passed.  Direct axiom audit reports `[propext, Classical.choice, Quot.sound]`
for the new public theorem names.

## Nonclaims

This is only the zero-tail (`M = 0`) `F3` bridge.  It does not prove the
positive-tail `F3` bridge, full raw-tuple equality, actual raw-order Frechet
determinant equality, source measure transport, normal crossings, pole order,
or RLCT.  The positive-tail case still needs a post-`Ctop` linear-map package
for the early lower-left derivative `dEarly_postC`.
