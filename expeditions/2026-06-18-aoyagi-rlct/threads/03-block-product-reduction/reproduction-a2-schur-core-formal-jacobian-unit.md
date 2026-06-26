# Reproduction - A2 Schur-core formal Jacobian unit

Date: 2026-06-26.

Status: pen-and-paper reproduced; formalised in Lean; xhigh review passed after
finite-side determinant-hypothesis repair.

## Source Anchor

Aoyagi Lemma 2, PDF pp. 10-11, performs the local Schur-complement coordinate
change on the determinant chart `det(A1) != 0`.  The same Schur move is then
repeated in the proof of Theorem 3 on pp. 12-13.

For this slice, fix the invertible top-left block

```text
B = A1 : Mat_r
```

and keep only the Schur core variables

```text
A2 : Mat_{r,n},   A3 : Mat_{m,r},   A4 : Mat_{m,n}.
```

Aoyagi's displayed coordinate change is

```text
F2 = -B^{-1} A2,
F3 = -A3 B^{-1},
C4 = A4 - A3 B^{-1} A2.
```

This is the fixed-pivot core behind the larger product-reduction step.  It does
not include the previously accumulated `C1`, `D`, or `F3_old` bookkeeping.

## Formal Tangent Calculation

At fixed base point `(B,A2,A3,A4)`, a tangent vector is

```text
(dA2, dA3, dA4).
```

Since `B` is fixed in this core calculation, the formal differential is

```text
dF2 = -B^{-1} dA2,
dF3 = -dA3 B^{-1},
dC4 = dA4 - dA3 B^{-1} A2 - A3 B^{-1} dA2.
```

The inverse formulas for the coordinate change are

```text
A2 = -B F2,
A3 = -F3 B,
A4 = C4 + F3 B F2.
```

Linearizing these at `F2 = -B^{-1}A2` and `F3 = -A3B^{-1}` gives the inverse
tangent map

```text
dA2 = -B dF2,
dA3 = -dF3 B,
dA4 = dC4 - dF3 A2 - A3 dF2.
```

## Inverse Checks

Starting with `(dA2,dA3,dA4)`, apply the forward tangent map and then the
inverse tangent map.

For `dA2`,

```text
-B(-B^{-1}dA2) = B(B^{-1}dA2) = dA2.
```

For `dA3`,

```text
-(-dA3B^{-1})B = dA3(B^{-1}B) = dA3.
```

For `dA4`,

```text
(dA4 - dA3B^{-1}A2 - A3B^{-1}dA2)
  - (-dA3B^{-1})A2
  - A3(-B^{-1}dA2)
= dA4.
```

Conversely, starting with `(dF2,dF3,dC4)` and applying the inverse tangent map
then the forward tangent map:

```text
-B^{-1}(-B dF2) = dF2,
-(-dF3 B)B^{-1} = dF3,
```

and

```text
(dC4 - dF3A2 - A3dF2)
  - (-dF3B)B^{-1}A2
  - A3B^{-1}(-B dF2)
= dC4.
```

All cancellations use only

```text
B B^{-1} = 1,    B^{-1} B = 1,
```

which are available from `IsUnit det(B)`.  No residual block is inverted.

## Lean Target

The Lean theorem lives in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`.

It defines the common tangent space

```text
SchurCoreTangent = Matrix ρ ν K × (Matrix μ ρ K × Matrix μ ν K)
```

and proves:

```text
schurCoreFormalJacobian
schurCoreFormalJacobianInverse
schurCoreFormalJacobianEquiv
schurCoreFormalJacobian_det_isUnit
```

The determinant-unit theorem follows from packaging the formal tangent map as a
`LinearEquiv` and applying `LinearEquiv.isUnit_det'`.

The `LinearEquiv` statement is meaningful for arbitrary side index types, but
the determinant-unit theorem is restricted to finite `mu` and `nu` indices.
This matches Aoyagi's finite matrix Jacobian calculation and avoids Lean's
general determinant fallback outside finite-dimensional spaces.

## Boundary

This proves the fixed-`B` Schur-core formal Jacobian is nonvanishing on the
determinant chart.  It does not prove:

- the full p. 13 product-step tangent map with variable `C1`, `A1`, `D`, and
  `F3_old`;
- `HasFDerivAt` for the nonlinear chart map;
- a source-measure pushforward;
- transported density bounds;
- chart coverage;
- normal crossings, pole order, or RLCT extraction.
