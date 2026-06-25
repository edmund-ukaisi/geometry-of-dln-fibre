# Reproduction - A2 residual block continuity support

Date: 2026-06-25.

Status: pen-and-paper reproduction for the local continuity support and
source-dependent p.13 product-coordinate family continuity.

## Source Boundary

This is an elementary finite-dimensional topology slice for Aoyagi's p.13
product-coordinate construction.  It proves that the transformed Schur
residual blocks and their ordered residual product vary continuously with the
base edge matrices, provided the recursive determinant-chart hypotheses hold
at the base point.  It then assembles those residual-block facts with the
continuous Euclidean regular-coordinate blocks and the fixed-base matrix
realisation map to prove local `(x,u)` continuity of the constructed
source-dependent product-coordinate edge family.

It does not prove a product chart, source coverage, rank-stratum openness,
automatic recursive chart neighborhoods, signed-box pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT extraction.

## Calculation

Let

```text
E(x)_p : Matrix (rho + kappa_{p+1}) (rho + kappa_p)
```

be a continuous family of fixed-coordinate edge matrices.  The suffix
recursion forms

```text
S(x;i) = suffixState(E(x), j, i)
```

by repeatedly transforming an edge and taking Schur-complement data.  The only
non-polynomial operation is inversion of the selected top-left block.  Thus
continuity at `x0` requires the recursive determinant-chart conditions

```text
identityCornerDetChart
  (transformedEdge(E(x0), p, suffixState(E(x0), j, p+1))).
```

Under these hypotheses the existing suffix-state topology theorem gives
continuity of all fields of `S(x;i)`, in particular `B`, `Ctop`, and `D`.

For a fixed edge `p`, the transformed Schur residual factor is

```text
residualBlock(E(x), j, p)
  = schurResidualBlock(transformedEdge(E(x), p, S(x;p+1))).
```

The map `x ↦ transformedEdge(E(x), p, S(x;p+1))` is continuous because it is
assembled from `E(x)_p` and the continuous `B` field of `S`.  On the selected
determinant chart, `schurResidualBlock` is continuous:

```text
lowerRight - lowerLeft * topLeft^{-1} * upperRight.
```

Therefore each transformed residual factor is continuous at `x0`.

The residual product is already the `D` field of the suffix state:

```text
suffixState(E(x), j, i).D = residualProduct(E(x), j, i).
```

Hence continuity of the `D` field gives continuity of the residual product.

For fixed endpoint bases, a continuous reversed edge family `Cedge(x)` gives
continuous fixed-coordinate matrices by applying continuous matrix-coordinate
functionals.  Composing this with the generic residual-block continuity result
gives fixed-base continuity of each source residual factor.

For the source-dependent multi-edge p.13 constructor, set

```text
Ebase(x) = fixedBaseEdgeMatrix(CedgeBase(x)).
```

At `(x,u)` the prescribed fixed-base product-coordinate matrix family has
three cases:

```text
right endpoint: [I, 0; -F3(u), residualBlock(Ebase(x), last, lastEdge)]
middle edge:    [I, 0; 0,       residualBlock(Ebase(x), last, p)]
left endpoint:  [Ctop(u), -Ctop(u)F2(u); 0,
                 residualBlock(Ebase(x), last, 0)].
```

The blocks `F2(u)`, `F3(u)`, and `Ctop(u)` are continuous in Euclidean
regular coordinates.  The residual blocks are continuous in `x` under the
recursive determinant-chart hypotheses for `Ebase(x0)`.  The three raw p.13
matrix patterns are polynomial in these entries, hence the whole prescribed
matrix family is continuous at `(x0,u0)`.

Finally, fixed endpoint bases identify prescribed matrices with continuous
linear maps continuously: apply `Matrix.toLin` in the fixed bases and then
`LinearMap.toContinuousLinearMap`.  Composing this realisation map with the
continuous prescribed matrix family gives continuity of
`CedgeProd(x,u)`.

In the self-base case, where

```text
CedgeBase(x0) = reverseEdge(B),
```

the recursive determinant-chart hypotheses are supplied by the existing
fixed-base self-base chart theorem.  This yields the same `CedgeProd`
continuity statement without exposing the recursive chart hypotheses as
separate inputs.

## Lean Target

New generic topology lemmas:

```text
continuous_productCoordinateRightEndpointMatrix
continuous_productCoordinateMiddleMatrix
continuous_productCoordinateLeftEndpointMatrix
continuousAt_chartLocalSuffixState_residualBlock
continuousAt_chartLocalSuffixState_residualProduct
continuous_matrix_toContinuousLinearMap
```

New fixed-base continuity lemmas:

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousAt
paperEndpointFixedBaseContinuousEdges_residualBlock_continuousAt
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuous
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuousAt
```

New regular-coordinate projection support:

```text
AoyagiRegularBlockCoordinateIndex.continuous_f2Matrix_euclidean
AoyagiRegularBlockCoordinateIndex.continuous_f3Matrix_euclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
```

## Boundary

The recursive determinant-chart hypotheses are explicit and local.  Continuity
does not follow from `ContinuousAt Cedge x0` alone unless those chart
hypotheses are also supplied or obtained from a separate local chart theorem.
The local continuity theorem keeps the recursive determinant-chart hypotheses
explicit.  The `Ctop(u)` determinant neighborhood is separate: it enables
coordinate readout for the product family near `u = 0`, but it does not ensure
continuity of the base residual factors or prove the recursive chart
hypotheses automatically near `x0`.
