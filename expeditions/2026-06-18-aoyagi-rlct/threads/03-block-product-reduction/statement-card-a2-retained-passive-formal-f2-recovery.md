# Statement Card - A2 retained-passive formal F2 recovery

Status: reproduced and Lean-proved; xhigh review pending.

## Claim

For `z` in the retained-passive determinant chart, the point-specialized formal
raw-order map recovers each source `F2` tangent from the formal target `(F2,C)`
edge pair:

```text
let u := retainedPassiveFormalRawOrderJacobianAt z v
(coord.solvedA1 p)^-1 *
  (coord.F2 p.succ * u.C_p - u.F2_p)
= v.F2_p.
```

The determinant-chart hypothesis supplies invertibility of
`coord.solvedA1 p`.

## Lean Status

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

New name:

```text
retainedPassiveFormalRawOrderJacobianAt_recovers_F2
```

Focused local build passed:

```text
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
```

## Dependencies

- formal raw-order apply formula
  `retainedPassiveFormalRawOrderJacobian_apply`;
- determinant-chart invertibility
  `solvedA1_det_isUnit_of_detChart`;
- matrix inverse cancellation
  `Matrix.nonsing_inv_mul_cancel_left`;
- elementary matrix distributivity and additive cancellation.

## Nonclaims

This is a formal-map recovery identity only.  It does not prove a target-side
shear, determinant equality, actual derivative determinant, measure theorem,
normal-crossing theorem, pole-order theorem, or RLCT result.
