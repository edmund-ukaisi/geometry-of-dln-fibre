# Statement Card - A2 retained-passive positive-tail post-`Ctop` `F3` shear

Status: PROVED in Lean, pending independent review.

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Main Lean names:

```text
retainedPassivePostCtopF3PosShearRawTupleLinearEquivAt
retainedPassivePostCtopF3PosShearRawTupleLinearEquivAt_apply
retainedPassivePostCtopF3PosShearRawTupleLinearEquivAt_det_eq_one
retainedPassivePostCtopF3PosShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShearRawTupleLinearEquivAt
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShearRawTupleLinearEquivAt_apply
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShearRawTupleLinearEquivAt_abs_det_eq_one
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShear_fderiv_F3_eq_formalRawOrderJacobianAt
```

Mathematical content:

- For passive-tail length `M + 1`, the post-`Ctop` `F3` stage fixes all raw
  tuple fields except `F3`.
- The `F3` correction is

```text
- dEarly_postC(rest) * coord.solvedA1(Fin.last (M + 1))
  + (coord.F3 - Earlyfun z) * rest.A1passive(Fin.last M).
```

- The shear has determinant and absolute determinant equal to one.
- After composing with the edge-pair, `A1passive`, and `Ctop` stages, the
  `F3` component of `(fderiv raw z) v` agrees with the formal raw-order
  Jacobian's `F3` component.

Inputs used:

- The post-`Ctop` recursive `dEarly` comparison at `m = 0`.
- `F3` preservation through the first three target-side stages.
- Terminal passive `A1` preservation through the `Ctop` stage.
- The existing target-only positive-tail `F3` theorem.

Nonclaims:

- This card does not claim a single full raw-tuple equality theorem.
- This card does not claim actual Frechet determinant equality for the complete
  coordinate change.
- This card does not claim measure transport, normal crossings, pole order, or
  RLCT.
