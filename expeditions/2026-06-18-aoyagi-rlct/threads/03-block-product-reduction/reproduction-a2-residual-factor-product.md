# Reproduction - A2 residual-factor product

Date: 2026-06-25.

Status: controller pen-and-paper reproduction before/alongside Lean.  This is
chart-local product-coordinate algebra only.

## Source/Boundary Anchor

Aoyagi's p.13 product-reduction display separates the regular coordinates
from the lower-right residual product.  In the current Lean development, the
lower-right residual coordinate map is controlled by
`ChartLocalSuffixState.residualProduct`, which is defined as the decreasing
ordered product of the Schur residual blocks visited by the deterministic
suffix recursion.

This checkpoint does not identify that product with Aoyagi's selected-entry
matrix.  It only names the elementary intermediate-factor product:
if a product-coordinate edge family has residual factors `C_p`, then its
suffix residual product is the ordered product of those supplied factors.

## Pen-And-Paper Check

Fix a chain with residual index types `kappa_i`.  For each edge
`p : Fin N`, suppose we are given a factor

```text
C_p : Matrix(kappa_{p+1}, kappa_p).
```

Define the explicit factor product from endpoint `j` down to `i <= j` by
starting at the identity matrix on `kappa_j` and multiplying the factors in
decreasing order:

```text
R(j,j) = I,
R(j,p) = R(j,p+1) C_p.
```

The Lean definition `residualFactorProduct C j i` is this recursion.

Now let `E` be a raw p.13 product-coordinate edge family with the displayed
forms:

```text
right endpoint: E_last = [ I   0  ; -F3   C_last ],
middle edge:    E_p    = [ I   0  ;  0    C_p    ],
left endpoint:  E_0    = [ Ctop  -Ctop F2 ; 0  C_0 ].
```

The already-proved Schur-block calculation says that, for every edge in this
full suffix, the transformed Schur residual block is exactly the supplied
factor:

```text
residualBlock(E, j, p) = C_p.
```

Therefore the recursive definition of `residualProduct` unfolds as

```text
residualProduct(E,j,j) = I,
residualProduct(E,j,p) =
  residualProduct(E,j,p+1) residualBlock(E,j,p)
  = residualFactorProduct(C,j,p+1) C_p
  = residualFactorProduct(C,j,p).
```

Descending induction on `p` gives

```text
residualProduct(E,j,i) = residualFactorProduct(C,j,i).
```

In particular, for the full p.13 multi-edge product-coordinate chain,

```text
residualProduct(E,last,0) = residualFactorProduct(C,last,0).
```

## Lean Target

Add in `ProductReduction.lean`:

```text
ChartLocalSuffixState.residualFactorProduct
ChartLocalSuffixState.residualFactorProduct_self
ChartLocalSuffixState.residualFactorProduct_castSucc
ChartLocalSuffixState.residualProduct_eq_residualFactorProduct_of_residualBlock_eq
ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_residualFactorProduct
```

## Boundary

- This is finite chart-local product-coordinate algebra.
- It does not construct the residual factors from Aoyagi source data.
- It does not prove that the factor product is a selected-entry matrix.
- It does not construct a fixed-base source chart or residual-index
  equivalence.
- It does not prove source coverage, source-measure transport, normal
  crossings, pole order, or RLCT.
