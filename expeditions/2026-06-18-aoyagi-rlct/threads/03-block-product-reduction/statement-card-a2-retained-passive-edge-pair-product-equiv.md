# Statement Card - A2 retained-passive edge-pair product equivalence

Status: reproduced, Lean-proved, and xhigh-reviewed.

## Claim

If each `A p` has determinant a unit, then the dependent product of edge-local
maps

```text
(F_p,C_p)_p |->
  (-(A_p + H_p*G_p)*F_p + H_p*C_p,
   -G_p*F_p + C_p)_p
```

is a linear equivalence.  After regrouping edge pairs into raw-order
`(F2,C)` families, the inverse is

```text
F_p = A_p^{-1} * (H_p*C'_p - F'_p),
C_p = C'_p + G_p * (A_p^{-1} * (H_p*C'_p - F'_p)).
```

## Lean Target

Expected Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalLinearDeterminant.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalRawOrder.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

Expected Lean names:

```text
edgeLocalFCPairPiLinearEquiv
edgeLocalFCPairPiLinearEquiv_apply
edgeLocalFCPairPiLinearEquiv_symm_apply
retainedPassiveFormalRawF2CLinearEquiv
retainedPassiveFormalRawF2CLinearEquiv_apply
retainedPassiveFormalRawF2CLinearEquiv_symm_apply
retainedPassiveFormalRawF2CLinearEquivAt
retainedPassiveFormalRawF2CLinearEquivAt_apply_sourcePair
retainedPassiveFormalRawF2CLinearEquivAt_symm_apply
retainedPassiveFormalRawF2CLinearEquivAt_symm_recovers_sourcePair
```

## Dependencies

- `edgeLocalFCPairLinearEquiv`;
- `LinearEquiv.piCongrRight`;
- retained-passive edge regrouping
  `retainedPassiveFormalEdgeTangentLinearEquiv`;
- determinant-chart unit theorem for `coord.solvedA1 p`;
- `retainedPassiveFormalRawOrderJacobian_apply`.

## Kill Conditions

- If the theorem claims anything about the actual Frechet derivative
  determinant, it overclaims.
- If the inverse uses the first-edge passive tail instead of
  `coord.solvedA1 p`, it has the wrong edge-local diagonal factor.
- If it treats `Ctop` or terminal `F3` as included in the edge-pair product,
  it has exceeded its scope.

## Nonclaims

No actual derivative determinant comparison, no full retained-passive
target-side factorization, no measure theorem, no normal crossings, no pole
order, and no RLCT follows from this edge-pair product equivalence alone.
