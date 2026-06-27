# Statement Card - A2 retained-passive formal C recovery

Status: reproduced, Lean-proved, and xhigh-reviewed.

## Claim

For `z` in the retained-passive determinant chart, the point-specialized formal
raw-order map recovers each source `C` tangent from the formal target `(F2,C)`
edge pair after substituting the recovered `F2` tangent:

```text
let u := retainedPassiveFormalRawOrderJacobianAt z v
u.C_p
  + coord.solvedA3 p *
      ((coord.solvedA1 p)^-1 *
        (coord.F2 p.succ * u.C_p - u.F2_p))
= v.C_p.
```

## Lean Status

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Lean theorem:

```text
retainedPassiveFormalRawOrderJacobianAt_recovers_C
```

Focused local build passed:

```text
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
```

## Dependencies

- `retainedPassiveFormalRawOrderJacobianAt_recovers_F2`;
- formal raw-order `C` component formula from
  `retainedPassiveFormalRawOrderJacobian_apply`;
- additive cancellation in finite matrix spaces.

## Nonclaims

This is a formal-map recovery identity only.  It does not prove a target-side
linear shear, determinant equality, actual Frechet derivative determinant,
measure theorem, normal crossings, pole order, or RLCT.
