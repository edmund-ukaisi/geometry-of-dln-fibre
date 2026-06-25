# Reproduction - A2 continuous-edge signed-box adapted-loss finite integral

Date: 2026-06-25.

Status: pen-and-paper reproduction for the composed finite-integral front end.

## Source Boundary

This is the top p.13 finite-integral plumbing theorem for the current A2
local-measure stack.  It combines four previously separated inputs:

1. global continuity of the fixed-base edge family, used only to derive
   source-stratum measurability and fixed-basis edge-matrix measurability;
2. a signed-box residual source chart, used only to derive residual positivity
   and residual negative-power integrability;
3. positivity and continuity of the product density at `(x0,0)`, used only to
   shrink the regular-coordinate radius and produce local density bounds;
4. a supplied comparison from the adapted p.13 square-sum to the chosen loss.

The hard analytic comparison remains an explicit hypothesis:

```text
c0 * adaptedProductDifferenceSquareSum(CedgeProd(x,u)) <= loss(x,u).
```

## Calculation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
res(x) = residualSquareSum(x)
A(x,u) = adaptedProductDifferenceSquareSum(CedgeProd(x,u)).
```

Global `Continuous Cedge` gives:

```text
MeasurableSet S,
Measurable edgeMatrix(x)
```

where `edgeMatrix(x)` is the fixed-basis endpoint matrix family used by the
deterministic suffix-state residual map.

The weighted signed-box source theorem then uses the supplied pushforward

```text
mu.restrict S
  = map sourceChart (signedBox.withDensity (ofReal sourceDensity))
```

and the monomial residual/density bounds to prove

```text
forall^ae x d(mu.restrict S), 0 < res(x),
int^- ofReal(res(x)^(-t)) d(mu.restrict S) < infinity.
```

The product-coordinate lower-bound hypotheses are

```text
c * (res(x) + squareSum(u)) <= A(x,u),
c0 * A(x,u) <= loss(x,u),
```

on the source filter and `ball(0,Rmax)`.  Since `0 < c0`, multiplying the
first inequality by `c0` and composing gives

```text
(c0 * c) * (res(x) + squareSum(u)) <= loss(x,u).
```

The positive continuous density theorem shrinks to `R <= Rmax` and supplies
local `0 <= density <= C`.  The p.13 finite-integral theorem applies at radius
`R`.

## Lean Shape

The formal theorem is

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

It calls the residual signed-box constructor and then delegates to the
continuous-density adapted-loss comparison theorem.

## Boundaries

This theorem is still conditional finite-integral plumbing.  It does not prove
the signed-box chart, the pushforward identity, density/Jacobian transport, the
adapted-to-original-loss comparison, source-rank openness, a product chart,
normal crossings, pole order, or RLCT extraction.

