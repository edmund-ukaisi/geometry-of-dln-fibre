# Reproduction - A2 adapted product-difference local finite-integral handoff

Date: 2026-06-25.

Status: pen-and-paper reproduction for a conditional finite-integral handoff.

## Source Anchor

Aoyagi p. 13 separates the residual product variables from the regular
variables.  The finite-side p.13 theorem already formalised in Lean consumes a
product-coordinate loss lower bound of the form

```text
c * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u)
```

uniformly for `u` in a small regular-coordinate ball.  The newly landed
self-base adapted fixed-base comparison gives a lower bound only for actual
source points; by itself it does not introduce an independent regular fiber
variable `u`.

## Product-Coordinate Boundary

Let

```text
A(y) = paperEndpointFixedBaseAdaptedProductDifferenceSquareSum(y).
```

To use `A` as a product-coordinate loss, we must supply a product edge-family
or chart-like map

```text
CedgeProd : alpha x regularEuclidean -> edge family
```

and a chart loss `chartLoss` satisfying, on the source filter and for
`u` in a fixed ball,

```text
c * (residualSquareSumBase(x) + squareSum(u))
  <= A(CedgeProd(x,u)),

A(CedgeProd(x,u)) = chartLoss(x,u).
```

These are hypotheses.  They are not derived from the base-only self-base
comparison.

The residual base hypotheses are the same as for the existing p.13 local
finite-integral theorem:

```text
residualSquareSumBase(x) > 0   a.e. on the source stratum,
int^- residualSquareSumBase(x)^(-t) < infinity,
```

with `t > 0`, a measurable source stratum, a positive regular radius, and
bounded nonnegative density on the product ball.

## Derivation

Intersect the two eventual source-filter hypotheses

```text
hadapted_lower
hloss_id
```

and rewrite the adapted square-sum to `chartLoss`.  This gives exactly the
`hloss` input of the existing theorem

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top.
```

The existing theorem then shrinks to an open source neighborhood `U` and proves

```text
int^- (x,u) over (mu.restrict (U inter sourceStratum)).prod nu,
  ofReal(1_{ball(0,R)}(u)
    * chartLoss(x,u)^(-(t + regularCount/2))
    * density(x,u))
  < infinity.
```

## Lean Shape

Lean should add a theorem in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

inside `PaperEndpointFixedBaseRegularCoordinateSourceData`, near the existing
local finite-integral bridge.  Expected name:

```text
exists_open_lintegral_ofReal_chartLoss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_identified
```

The theorem takes `CedgeBase` from `sourceData`, an independent `CedgeProd` on
`alpha x regularEuclidean`, the explicit `hadapted_lower`, the explicit
`hloss_id`, and the existing residual/density hypotheses, and delegates to the
already-landed local finite-integral theorem.

## Boundary

This theorem does not construct a product chart, prove source coverage,
identify coordinates, prove a Jacobian/prior density formula, prove residual
positivity or residual negative-power integrability, compare with original
`lossDLN`, produce normal crossings, compute pole order, or extract an RLCT.
