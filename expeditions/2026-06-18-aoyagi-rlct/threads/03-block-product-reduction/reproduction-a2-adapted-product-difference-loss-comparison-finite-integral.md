# Reproduction - A2 adapted product-difference loss-comparison finite integral

Date: 2026-06-25.

Status: pen-and-paper reproduction for a conditional finite-integral handoff.

## Source Boundary

Aoyagi p. 13 displays the regular-suspension split after the product
reduction.  The current Lean development has a p.13 finite-integral theorem
which consumes a product-coordinate loss lower bound

```text
c * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u).
```

The original DLN/statistical loss has not yet been identified with the p.13
adapted product-difference square-sum.  The safe boundary is therefore
conditional: assume explicitly that, on the same source-neighborhood filter
and regular-coordinate ball,

```text
c0 * adaptedProductDifferenceSquareSum(CedgeProd(x,u)) <= loss(x,u),
```

with `c0 > 0`.

## Calculation

Write

```text
R(x,u) = residualSquareSum(x) + regularSquareSum(u)
A(x,u) = adaptedProductDifferenceSquareSum(CedgeProd(x,u)).
```

Assume the supplied product-coordinate adapted lower bound

```text
c * R(x,u) <= A(x,u)
```

with `c > 0`.  Since `0 <= c0`, multiplication on the left by `c0` preserves
the inequality:

```text
c0 * (c * R(x,u)) <= c0 * A(x,u).
```

Combining with the supplied loss comparison gives

```text
c0 * (c * R(x,u)) <= loss(x,u).
```

Reassociating constants,

```text
(c0 * c) * R(x,u) <= loss(x,u),
```

and `0 < c0 * c` by positivity of both constants.  This is exactly the loss
lower-bound hypothesis required by the existing p.13 finite-integral theorem.

## Lean Shape

The formal theorem is in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

with name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss
```

It takes the existing residual source hypotheses, local density bounds, product
edge-family `CedgeProd`, the supplied adapted lower bound, and the supplied
comparison `c0 * adapted <= loss`.  It delegates to

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
```

with comparison constant `c0 * c`.

## Boundaries

This theorem does not prove the original-loss comparison.  It assumes it.
It also does not construct the p.13 product chart, identify chart coordinates,
prove source coverage, prove density or Jacobian transport, prove residual
positivity or residual negative-power integrability, construct a
normal-crossing chart family, compute pole order, or extract an RLCT.

