# Reproduction - A2 original loss local measure handoff

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean implementation; independent
review passed.

## Source Anchor

This is the finite bridge from Aoyagi's p.13 adapted product-difference loss
to the repository's original square-Frobenius `lossDLN`, in the local
finite-integral theorem already developed for the p.13 regular coordinates.
It is not a new analytic chart theorem.  The only new step is to discharge the
previously supplied comparison

```text
c0 * adaptedProductDifferenceSquareSum <= loss
```

for the specific original loss

```text
lossDLN d [T(B)]_b (chainMapMatrixTuple b E).
```

## Derivation

Let `E(z)` be the reversed-edge family supplied by the product-coordinate map
`CedgeProd z`, and let

```text
T(E(z)) = chainMap(reverseVertex W, E(z), 0, last),
T(B)    = chainMap(reverseVertex W, reverseEdge W B, 0, last).
```

The generic p.13 local-measure front end already proves local finiteness for a
loss `L(z)` once the following source-filter comparison is available on a
smaller source neighborhood and uniformly for the regular coordinate fiber:

```text
c0 * paperEndpointFixedBaseAdaptedProductDifferenceSquareSum(z)
  <= L(z).
```

The endpoint loss comparison gives a stronger pointwise global fact for the
original square-Frobenius loss.  For fixed original bases
`b j : Basis (Fin (d j)) R (reverseVertex W j)`, there is `c0 > 0` such that
for every `z`,

```text
c0 * paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss(z)
  <= lossDLN d [T(B)]_b (chainMapMatrixTuple b E(z)).
```

The fixed-base Frobenius identification rewrites

```text
paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss(z)
  =
paperEndpointFixedBaseAdaptedProductDifferenceSquareSum(z).
```

Therefore the generic comparison hypothesis is obtained with

```text
L(z) =
lossDLN d [T(B)]_b (chainMapMatrixTuple b E(z)).
```

The comparison is pointwise, so it is also true eventually on the
`nhdsWithin x0 sourceStratum` filter and uniformly on the ball
`u in ball(0,Rmax)`.  The rest of the theorem is exactly the already-proved
adapted-loss local-measure theorem: residual source data, signed-box
pushforward data, transported density positivity/continuity, and the p.13
product-coordinate adapted lower bound remain explicit hypotheses.

## Lean Shape

Lean implements the wrapper in

```text
lean/DLNFibre/DLN/Aoyagi/OriginalLossLocalMeasure.lean
```

with names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
```

Both wrappers build the local abbreviation

```text
target = [T(B)]_{b 0,b last}
originalLoss z = lossDLN d target (chainMapMatrixTuple b (CedgeProd z))
```

and use

```text
exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
```

to provide the comparison hypothesis for the generic theorem in
`RegularSuspensionLocalMeasure.lean`.

## Boundary

This proves local finite lower-integral control only for original
square-Frobenius `lossDLN` on tuples of the form
`chainMapMatrixTuple b (CedgeProd z)`, with target matrix the base endpoint
chain map expressed in the same endpoint bases `b`.

It still assumes the p.13 product-coordinate adapted lower bound, signed-box
source chart and weighted pushforward, residual monomial lower bound,
source-density bounds, positive continuous transported density, and residual
source hypotheses through the existing front end.  It does not construct the
chart, prove density/Jacobian transport, compare statistical/KL/covariance
losses, handle arbitrary tuples, produce normal crossings, compute pole order,
or extract an RLCT.
