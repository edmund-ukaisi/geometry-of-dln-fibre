# Reproduction - A2 fixed-base prescribed edge-matrix realisation

Date: 2026-06-25.

Status: pen-and-paper reproduction for the finite basis inverse that turns
prescribed fixed-base edge matrices back into fixed-base edge maps.

## Calculation

Fix endpoint bases `b_i` for `reverseVertex(i)`.  For a prescribed edge matrix

```text
G_p : Matrix(index(p.succ), index(p.castSucc), K),
```

define the reversed edge map by the inverse matrix-to-linear-map equivalence:

```text
E_p = Matrix.toLin b_{p.castSucc} b_{p.succ} G_p.
```

Mathlib's inverse law gives

```text
LinearMap.toMatrix b_{p.castSucc} b_{p.succ} E_p = G_p.
```

Since the source module is finite-dimensional over the complete normed field,
the same linear map can be regarded as a continuous linear map.  Coercing
`LinearMap.toContinuousLinearMap E_p` back to a linear map is definitionally
`E_p`, so the fixed-base edge-matrix readout is still exactly `G_p`.

Therefore a pointwise product-family matrix theorem can be used with an actual
fixed-base continuous edge family: build `Cedge` from the prescribed edge
matrices `G`, recover `EMat = G`, and feed the already-proved product-family
suffix-field/coordinate readout theorem.

## Lean Target

```text
paperEndpointFixedBaseReverseEdgeFamilyOfMatrices
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_reverseEdgeFamilyOfMatrices
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_prescribedProductFamilyEdgeMatrices_succSucc
```

## Boundary

This does not define the final product-coordinate family `G(x,u)`.  It does
not prove the transformed-edge block-shape hypotheses for such a family, does
not prove parameter-continuity of a matrix-valued family, and does not prove
source coverage, signed-box pushforward, density/Jacobian transport, normal
crossings, pole order, or RLCT extraction.

An attempted convenience theorem for a fully parameterized `G : alpha -> ...`
was deliberately not kept: the pointwise theorem is enough for the next layer,
and unfolding the full coordinate map in that wrapper created pathological
Lean elaboration.
