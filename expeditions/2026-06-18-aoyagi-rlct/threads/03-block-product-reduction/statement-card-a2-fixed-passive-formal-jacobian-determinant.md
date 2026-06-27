# Statement card - A2 fixed-passive formal Jacobian determinant

Status: reproduced, Lean-proved, and reviewed.

## Claim

For the fixed-passive p.13 formal tangent map
`productStepFixedPassiveFormalJacobian`, with raw variables
`(C1,F3old,A2,A4)` and chart variables `(Ctop,F3,F2,C)`, the raw-to-chart
determinant is

```text
det(A1)^(|rho|) * det(-A1^{-1})^(|nu|).
```

Equivalently, Lean proves

```text
LinearMap.det (productStepFixedPassiveFormalJacobian C1 D A1 A3)
  = A1.det ^ Fintype.card rho
    * (-A1^{-1}).det ^ Fintype.card nu.
```

## Lean status

Proved in `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`:

- `productStepFixedPassiveFormalJacobian_eq_shear_comp_diagonal`;
- `productStepFixedPassiveFormalJacobian_det_eq_multiplication_blocks`;
- `productStepFixedPassiveFormalJacobian_det_eq`.

The proof factors the formal map into one diagonal product map and two
determinant-one product shears.

## Dependencies

- fixed-passive formal tangent formulas in `ProductReductionStepJacobian.lean`;
- rectangular multiplication determinant lemmas from
  `MatrixLinearDeterminant.lean`;
- finite product-basis determinant arithmetic for product maps and shears.

## Caveats

This is the one-step fixed-passive determinant in raw-to-chart orientation.
It is not the full retained-passive raw-order determinant formula, not an
analytic `fderiv` theorem, not source-prior transport, not normal crossings,
not pole order, and not RLCT.
