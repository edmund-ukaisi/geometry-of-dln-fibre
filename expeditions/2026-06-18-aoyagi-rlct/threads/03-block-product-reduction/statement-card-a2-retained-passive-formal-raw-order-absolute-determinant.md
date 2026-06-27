# Statement Card: A2 Retained-Passive Formal Raw-Order Absolute Determinant

Status: reproduced and Lean-proved; review pending.

## Claim

The signed formal raw-order determinant formula for the retained-passive
block map has a sign-free absolute-value product form:

```text
|det J_formal| =
  |det(Tail^-1)|^|rho|
  * product_p |det(A p)|^|kappa' p.castSucc|
  * |det(LastTop)|^|kappa' last|.
```

The point-specialized theorem reads `Tail`, `A p`, and `LastTop` from a
retained-passive tuple `z` as

```text
Tail    = retainedPassiveA1TailAfterFirst data.A1seed
A p     = coord.solvedA1 p
LastTop = coord.solvedA1 (Fin.last M).
```

## Lean Status

Generic theorem in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalRawOrder.lean`:

```text
retainedPassiveFormalRawOrderJacobian_abs_det_eq
```

Point-specialized theorem in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`:

```text
retainedPassiveFormalRawOrderJacobianAbsDetAt_eq
```

## Dependencies

- `retainedPassiveFormalRawOrderJacobian_det_eq`;
- `Finset.abs_prod`;
- `abs_mul` and `abs_pow`;
- `Matrix.det_neg`, used only to remove the signs from edge-local and
  terminal factors after taking absolute values.

## Nonclaims

This checkpoint does not prove:

- `topologyTupleEdgeRawOrderFDerivAbsDet =
  retainedPassiveFormalRawOrderJacobianAbsDetAt`;
- equality of the analytic Frechet derivative with the formal raw-order map;
- a signed determinant formula in raw tuple order beyond the existing formal
  theorem;
- source-prior transport, source coverage, normal crossings, pole order, or
  RLCT.

## Verification Plan

1. Build `DLNFibre.DLN.Aoyagi.RetainedPassiveFormalRawOrder`.
2. Build `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`.
3. Run full `DLNFibre` build, forbidden-marker scan, and `git diff --check`.
4. Ask an xhigh reviewer to check that the theorem remains formal-only and
   does not overclaim the analytic determinant comparison.
