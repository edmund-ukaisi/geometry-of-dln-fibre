# Reproduction - A2 product-coordinate residual-product preservation

Date: 2026-06-25.

Status: Lean formalised after pen-and-paper check.  This is fixed-base
product-coordinate algebra only.

## Source/Boundary Anchor

The p.13 product-coordinate constructor packages regular coordinates
`F2`, `F3`, `Ctop` together with residual factors obtained from a base fixed
matrix family `Ebase`.  The important point is preservation: the constructed
product-coordinate matrices do not synthesize a new arbitrary final residual
matrix.  They preserve the suffix residual product already present in
`Ebase`.

## Pen-And-Paper Check

Let

```text
G = paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean(u,Ebase).
```

By the definition of `G`, its raw product-coordinate edge matrices have the
following residual factors:

```text
C_p = residualBlock(Ebase,last,p).
```

The right endpoint has form `[I,0;-F3,C_last]`, each middle edge has form
`[I,0;0,C_p]`, and the left endpoint has form
`[Ctop,-Ctop F2;0,C_0]`.  The chart-local product-coordinate theorem gives

```text
residualBlock(G,last,p) = residualBlock(Ebase,last,p)
```

for every visited edge `p`.  Applying equality of residual products from
equality of visited residual blocks gives

```text
residualProduct(G,last,0) = residualProduct(Ebase,last,0).
```

No determinant-unit hypothesis is needed for this identity: only the raw
matrix patterns and Schur residual block readout are used.

## Lean Target

Add in `RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq_base
```

## Boundary

- This is fixed-base product-coordinate residual-product preservation.
- It does not construct `Ebase`.
- It does not prove that the base residual product is a selected-entry matrix.
- It does not construct residual-index equivalence, source coverage, or
  source-measure transport.
- It does not prove normal crossings, pole order, or RLCT.
