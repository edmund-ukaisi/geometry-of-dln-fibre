# Reproduction - A2 original-loss local-source finite-integral socket

Date: 2026-06-25.

## Source Target

Aoyagi p.13 reduces the local zeta integral to regular product coordinates
and a residual block square-sum.  In the Lean development, the local-source
analytic-measure part is already isolated as

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_const_mul_adaptedProductDifferenceSquareSum_le_loss
```

That theorem assumes a local source set `source`, residual positivity and
negative-power integrability on `source`, a local lower bound from the residual
plus regular square-sum to the adapted product-difference square-sum, a local
positive comparison from the adapted square-sum to a supplied loss, and local
density bounds.

The next socket should specialize the supplied loss to the original endpoint
square-Frobenius loss `lossDLN` of the chain matrix tuple.

## Calculation

Let

```text
rho =
  AoyagiRegularBlockCoordinateIndex
    (Fin (finrank U0)) endpointComplement(last) endpointComplement(0)
```

and let the chart family be

```text
CedgeProd : alpha x EuclideanSpace R rho -> edges.
```

For a basis tuple `b`, define the fixed target matrix

```text
target = toMatrix (b 0) (b last) (chainMap base_edges).
```

Define the original loss on the product chart by

```text
originalLoss (x,u) =
  lossDLN d target
    (chainMapMatrixTuple b (fun p => CedgeProd (x,u) p)).
```

The finite endpoint basis comparison gives a constant `c0 > 0` such that for
all chart points `z`,

```text
c0 * adaptedFrobeniusLoss z <= originalLoss z.
```

The adapted Frobenius loss is definitionally equal to the adapted
product-difference square-sum:

```text
adaptedFrobeniusLoss (x,u)
  = paperEndpointFixedBaseAdaptedProductDifferenceSquareSum CedgeProd (x,u).
```

Therefore, for all `x` in any local source filter and all regular coordinates
`u` in the radius ball,

```text
c0 * paperEndpointFixedBaseAdaptedProductDifferenceSquareSum CedgeProd (x,u)
  <= originalLoss (x,u).
```

This is exactly the `hloss_cmp` input of the local-source adapted-loss socket.
No source shrinking, radius shrinking, density construction, or residual
source construction is involved in this step.

Combining the supplied local adapted lower bound

```text
c * (residualSquare x + regularSquare u)
  <= paperEndpointFixedBaseAdaptedProductDifferenceSquareSum CedgeProd (x,u)
```

with the comparison above is delegated to the existing local-source socket,
which internally multiplies the constants and applies the p.13 finite-side
integrability theorem.

## Lean Statement Shape

The Lean theorem should keep these inputs explicit:

- measurable local source set;
- residual positivity on `mu.restrict source`;
- residual negative-power integrability on `source`;
- local source-filter adapted lower bound;
- local source-filter density nonnegativity and upper bound;
- fixed endpoint bases, which supply the finite adapted-to-original comparison.

The conclusion is the finite integral of

```text
(lossDLN d target (chainMapMatrixTuple b (CedgeProd (z.1,u)))) ^
  (-(t + regularVariableCount / 2)) * density (z.1,u)
```

over `(mu.restrict (U inter source)).prod nu`, with the regular coordinate
indicator on the radius ball.

## Nonclaims

This socket does not construct the local source set, chart, weighted
pushforward, residual monomial identities, density/Jacobian transport,
adapted product-coordinate lower bound, normal crossings, pole order, or RLCT.
It is only the original-loss specialization of the local-source adapted-loss
finite-integral theorem.
