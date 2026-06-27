# A2 edge-local `(F,C)` pair determinant

Status: reproduced by controller; independently checked by xhigh
pen-and-paper scout; Lean-proved; reviewed.

## Scope

This note records the finite linear determinant calculation for the
retained-passive edge-local pair

```text
(F, C) |-> (Y12, Y22)
Y12 = -(A + H*G) * F + H * C
Y22 = -G * F + C.
```

It is only matrix-space linear algebra.  It is not an analytic derivative
theorem, source-prior pushforward, density formula, normal-crossing statement,
pole-order theorem, or RLCT theorem.

## Shapes and orientation

Let

```text
A : Matrix rho rho K
H : Matrix rho mu K
G : Matrix mu rho K
F : Matrix rho kappa K
C : Matrix mu kappa K.
```

Lean proves the determinant theorem over a `CommRing K`, with finite index
types `rho`, `mu`, and `kappa`.  The square determinant of `A` carries the
usual `Fintype rho` and `DecidableEq rho` assumptions.

The Lean-oriented input and output order is

```text
Matrix rho kappa K x Matrix mu kappa K,
```

with first coordinate `F` and second coordinate `C`.  The output is ordered as
`(Y12, Y22)`.  With this same order on domain and codomain, no permutation sign
is present.

## Factorization

Columnwise, the block matrix is

```text
[ -(A + H*G)   H ]
[     -G       I ].
```

It factors as

```text
[ I  H ] [ -A  0 ] [ I   0 ]
[ 0  I ] [  0  I ] [ -G  I ].
```

Equivalently, on matrix variables:

```text
(F, C) |-> (F, C - G*F)
(F, C) |-> (-A*F, C)
(F, C) |-> (F + H*C, C).
```

The composite is

```text
(F, C) |-> (-A*F + H*(C - G*F), C - G*F)
       = (-(A + H*G)*F + H*C, -G*F + C).
```

The two outer maps are triangular product shears, so their determinants are
`1`.  The middle map is left multiplication by `-A` on the `rho x kappa`
matrix coordinate and the identity on the `mu x kappa` coordinate.

## Determinant

Left multiplication by a `rho x rho` matrix on `rho x kappa` matrices
contributes the determinant of the multiplier to the number of columns:

```text
det(F |-> -A*F) = det(-A)^(|kappa|).
```

The `C` coordinate contributes `1`.  Therefore the edge-local pair determinant
in `(F,C)` to `(Y12,Y22)` orientation is

```text
det = det(-A)^(|kappa|).
```

Equivalently,

```text
det = (-1)^(|rho|*|kappa|) * det(A)^(|kappa|),
```

but the Lean theorem should keep the cleaner `det(-A)^(|kappa|)` form.

## Corner cases

The formula handles empty index types without special cases:

- if `kappa` is empty, the determinant is `1`;
- if `rho` is empty, `det(-A) = 1`;
- if `mu` is empty, the map reduces to left multiplication by `-A` on
  `Matrix rho kappa K`.

## Caveat on ordering

If only the input order or only the output order is swapped, a product-space
permutation sign is introduced.  That is not the orientation used here.

## Lean status

Lean now proves the finite determinant theorem in
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`.

New reusable helpers:

```text
moduleFinite_prod
linearMap_det_prodMap_eq_mul
linearEquiv_det_skewProd_toLinearMap_eq_mul
linearEquivUpperShear
linearEquivUpperShear_det_eq_one
```

New edge-local names:

```text
EdgeLocalFCPairTangent
edgeLocalFCPairLowerShear
edgeLocalFCPairDiagonal
edgeLocalFCPairUpperShear
edgeLocalFCPairLinearMap
edgeLocalFCPairLinearMap_apply
edgeLocalFCPairLowerShear_det_eq_one
edgeLocalFCPairUpperShear_det_eq_one
edgeLocalFCPairDiagonal_det_eq
edgeLocalFCPairLinearMap_det_eq
```

The final theorem is

```text
LinearMap.det (edgeLocalFCPairLinearMap A H G)
  = (-A).det ^ Fintype.card kappa.
```

Review:
`review-a2-edge-local-fc-pair-determinant.md`.

Verification:

- focused `MatrixLinearDeterminant` build passed;
- downstream `ProductReductionStepJacobian` build passed;
- full `DLNFibre` build passed with the existing warning profile;
- `scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
  `0 axiom`;
- `git diff --check` passed;
- axiom audit for `edgeLocalFCPairLinearMap_det_eq`,
  `linearEquivUpperShear_det_eq_one`, and
  `linearEquiv_det_skewProd_toLinearMap_eq_mul` reported
  `[propext, Classical.choice, Quot.sound]`.
