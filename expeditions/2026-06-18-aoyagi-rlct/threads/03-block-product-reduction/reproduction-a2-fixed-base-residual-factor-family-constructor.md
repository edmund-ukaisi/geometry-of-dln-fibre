# Reproduction - A2 fixed-base residual-factor family constructor

Date: 2026-06-25.

Status: Lean target implemented for the fixed-base raw p.13 constructor from
supplied compatible residual factors.

## Source Boundary

Aoyagi's p.13 product-reduction display isolates regular coordinates
`Ctop - I`, `F2`, and `F3`, and leaves the singular part as an ordered
product of residual factors `product_s C^(s)`.  Earlier Lean constructors
covered the self-base case where the residual factors are read from a base
edge family.  This note records the raw finite constructor for the more direct
source shape: the residual factors are supplied as finite matrices `Cfac p`.

This is still fixed-base matrix algebra.  It does not construct `Cfac` from a
selected-entry chart, does not prove a selected-entry factor-product identity,
and does not identify a local source image.

## Calculation

Let the p.13 chain have `M + 2` edges and endpoint

```text
j = Fin.last (M + 2).
```

Let `u` be the Euclidean vector of regular coordinates and set

```text
F2   = f2Matrix(u),
F3   = f3Matrix(u),
Ctop = ctopMatrix(u).
```

Let `Cfac p` be a supplied compatible residual factor

```text
Cfac p : Matrix kappa(p.succ) kappa(p.castSucc) R.
```

Define a fixed-base raw p.13 edge family `G(u,Cfac)` by the same right,
middle, and left endpoint patterns used in Aoyagi's product-coordinate
calculation:

```text
G(last) = productCoordinateRightEndpointMatrix F3 (Cfac last),
G(p)    = productCoordinateMiddleMatrix Cfac(p)      for middle p,
G(0)    = productCoordinateLeftEndpointMatrix F2 Ctop (Cfac 0).
```

The raw product-coordinate residual-block theorem applies directly to these
three shapes.  It gives, for every edge `p`,

```text
residualBlock(G(u,Cfac), j, p) = Cfac p.
```

The explicit residual-factor product theorem then gives

```text
residualProduct(G(u,Cfac), j, 0)
  = residualFactorProduct(Cfac, j, 0).
```

Thus the constructor realizes the supplied residual factors as the visited
transformed Schur residual blocks of a fixed-base p.13 matrix family, and the
suffix residual product is exactly their ordered product.

## Lean Target

Implemented in `RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean_residualBlock_eq
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean_residualProduct_eq_residualFactorProduct
```

The proof delegates to the raw product-reduction API:

```text
ChartLocalSuffixState.residualBlock_productCoordinateEdges_succSucc
ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_residualFactorProduct
```

## Nonclaims

- No construction of `Cfac` from selected-entry or source-chart coordinates.
- No proof that `residualFactorProduct Cfac last 0` is a selected-entry matrix.
- No residual-index equivalence construction.
- No source/image equality or finite chart cover for the p.13 source stratum.
- No source-measure transport, density/Jacobian identity, normal crossings,
  pole order, or RLCT.

## Follow-up

The next source-faithful target is a fixed displayed-pivot Case 2 factor
construction: identify the post-pivot residual block and following factor as
two compatible residual factors, then prove their ordered product equals the
displayed lower-row product.  The interrupted local `BlowupArithmetic.lean`
attempt exposed an API issue for a dependent `Fin 3` residual-index family and
was not included in this checkpoint.
