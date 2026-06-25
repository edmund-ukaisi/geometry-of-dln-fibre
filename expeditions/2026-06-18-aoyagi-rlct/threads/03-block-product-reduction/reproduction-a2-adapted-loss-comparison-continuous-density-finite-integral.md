# Reproduction - A2 adapted loss-comparison continuous-density finite integral

Date: 2026-06-25.

Status: pen-and-paper reproduction for a conditional radius-shrinking
finite-integral handoff.

## Source Boundary

The previous adapted-loss comparison bridge assumes local density bounds

```text
0 <= density(x,u),
density(x,u) <= C
```

on a source-filter neighborhood and a fixed regular-coordinate ball.  The
separate continuous-density p.13 theorem already proves that these bounds can
be obtained by shrinking the regular-coordinate radius when the transported
density factor is continuous and positive at `(x0,0)`.

This slice composes those two facts.  It does not prove the transported
density or the comparison from the adapted p.13 square-sum to the original
loss.

## Calculation

Assume `0 < Rmax`, `0 < c`, `0 < c0`, and on the source-rank
`nhdsWithin` filter, for all `u` in `ball(0,Rmax)`,

```text
c * (residualSquareSum(x) + squareSum(u))
  <= adaptedProductDifferenceSquareSum(CedgeProd(x,u)),
```

and

```text
c0 * adaptedProductDifferenceSquareSum(CedgeProd(x,u)) <= loss(x,u).
```

Continuity and positivity of `density` at `(x0,0)` give a smaller radius
`R` and a constant `C`, with

```text
0 < R,   R <= Rmax,   0 <= C,
0 <= density(x,u),   density(x,u) <= C
```

on the source filter and `ball(0,R)`.

Since `R <= Rmax`, the two loss-comparison hypotheses restrict from
`ball(0,Rmax)` to `ball(0,R)`.  The previous adapted-loss comparison bridge
then applies with comparison constant `c0 * c` and density bound `C`, producing
an open source neighborhood `U` and finiteness of

```text
int^- 1_{ball(0,R)}(u)
  * loss(x,u)^(-(t + regularCount/2))
  * density(x,u)
```

over `(mu.restrict (U inter sourceStratum)).prod nu`.

## Lean Shape

The target theorem should live in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

near the existing continuous-density p.13 theorem, with name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
```

It should call

```text
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
```

to produce `R,C` and then call

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss.
```

## Boundaries

This removes only explicit local density-bound hypotheses.  It still assumes
the adapted product-coordinate lower bound, the positive comparison from the
adapted square-sum to `loss`, residual positivity, residual negative-power
integrability, and source-stratum measurability.  It does not construct the
p.13 product chart, prove density/Jacobian transport, compare the adapted
square-sum with the original DLN/statistical loss, construct normal crossings,
compute pole order, or extract an RLCT.

