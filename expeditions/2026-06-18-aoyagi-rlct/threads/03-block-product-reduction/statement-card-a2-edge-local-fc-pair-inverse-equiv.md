# Statement Card - A2 edge-local `(F,C)` pair inverse equivalence

Status: reproduced, Lean-proved, and xhigh-reviewed.

## Claim

For `det A` a unit, the generic edge-local formal map

```text
(F,C) |-> (-(A + H*G)*F + H*C, -G*F + C)
```

is a linear equivalence.  Its inverse sends a target pair `(U,V)` to

```text
(A^{-1} * (H*V - U),
 V + G * (A^{-1} * (H*V - U))).
```

## Lean Status

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean
```

Lean names:

```text
edgeLocalFCPairLinearMapInverse
edgeLocalFCPairLinearMapInverse_apply
edgeLocalFCPairLinearEquiv
edgeLocalFCPairLinearEquiv_apply
edgeLocalFCPairLinearEquiv_symm_apply
```

Focused local builds passed:

```text
lake build DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
```

## Dependencies

- `edgeLocalFCPairLinearMap_apply`;
- matrix nonsingular inverse cancellation from `IsUnit A.det`;
- elementary matrix distributivity and additive cancellation.

## Nonclaims

This is finite linear algebra only.  It does not prove the retained-passive
total target-side shear, actual derivative determinant comparison, measure
theorem, normal crossings, pole order, or RLCT.
