# Reproduction - A2 multi-edge product-coordinate family constructor

Date: 2026-06-25.

Status: pen-and-paper reproduction for the fixed-base, fixed-`Ebase`
multi-edge p.13 product-coordinate constructor.

## Source Boundary

Aoyagi p.13 separates the product-difference coordinates into the regular
coordinates

```text
Ctop - I, F2, F3
```

and the residual product.  This note treats the at-least-two-edge case after a
fixed base edge-matrix family `Ebase` has already been chosen in the fixed
endpoint bases.  It constructs a new fixed-base matrix family whose regular
coordinate readout is a prescribed Euclidean vector `u` and whose residual
coordinate readout is the base residual product of `Ebase`.

It does not construct a source-dependent family `Ebase x`, prove continuity in
`(x,u)`, construct a product chart, prove source coverage, transport
density/Jacobian factors, produce normal crossings, prove pole order, or
extract RLCT.

## Calculation

Let the chain have `M + 2` edges and set

```text
j = Fin.last (M + 2).
```

Let `Ebase` be a fixed base family of fixed-coordinate edge matrices.  From a
Euclidean regular-coordinate vector `u`, define

```text
X  i j = u(inl(i,j)),
F2 i j = u(inr(inl(i,j))),
F3 i j = u(inr(inr(i,j))),
Ctop = I + X.
```

Then `Ctop - I = X`, so the regular-coordinate readout of
`(Ctop - I,F2,F3)` is exactly `u`.

For each edge `p`, choose the residual factor to be the base transformed Schur
residual block

```text
C(p) = residualBlock(Ebase, j, p).
```

Define the new raw edge matrix family `G(u,Ebase)` by Aoyagi's p.13 product
coordinate patterns:

```text
G(last) = [ I   0
            -F3 C(last) ],

G(p)    = [ I 0
            0 C(p) ]          for 0 < p.val < M+1,

G(0)    = [ Ctop  -Ctop F2
            0      C(0) ].
```

The raw product-coordinate edge-matrix theorem reads the fixed-base
product-difference coordinate map of the continuous edge family realised from
`G` as

```text
value(Ctop - I, F2, F3, residualProduct(G,j,0)).
```

The residual-product preservation theorem applies because every residual
factor of `G` was chosen as `residualBlock(Ebase,j,p)`.  Hence

```text
residualProduct(G,j,0) = residualProduct(Ebase,j,0).
```

Combining this with the Euclidean regular-coordinate reconstruction gives

```text
productDifferenceCoordinateMap(G(u,Ebase))
  =
Sum.elim (fun c => u c)
  (AoyagiResidualBlockCoordinateIndex.value (residualProduct(Ebase,j,0))).
```

The determinant hypothesis `IsUnit (Ctop(u)).det` is still required by the
coordinate-readout theorem.  It is not used by the residual-product
preservation statement itself.

## Lean Target

The fixed-base constructor and readout are:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_multiEdgeProductCoordinateEuclidean
```

The proof uses the already-landed raw edge and residual-product APIs:

```text
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields
ChartLocalSuffixState.suffixState_productCoordinate_fields_succSucc
ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_base
AoyagiProductDifferenceCoordinateIndex.value_euclideanCtopMatrixCoordinateMatrices_residual
```

The constructor is pointwise in `u` and `Ebase`; the continuous fixed-base edge
family is obtained by applying
`paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices` to the resulting
matrix family.

## Boundary

This is finite and pointwise for chains with at least two edges.  It does not
yet define the fully dependent source family `G(x,u)` from a base source edge
family `CedgeBase x`; that is the next wrapper.  It also does not prove
parameter-continuity, source chart status, signed-box pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT extraction.
