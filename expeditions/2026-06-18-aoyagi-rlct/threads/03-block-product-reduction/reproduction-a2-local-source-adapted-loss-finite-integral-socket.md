# Reproduction - A2 local-source adapted-loss finite-integral socket

Date: 2026-06-25.

## Scope

This slice is the local-source analogue of the existing adapted-loss
finite-integral socket.  It keeps the local source set explicit and proves only
the elementary comparison step that turns

```text
c * (residualSquareSum(x) + regularSquareSum(u)) <= adaptedLoss(x,u)
```

and

```text
c0 * adaptedLoss(x,u) <= loss(x,u)
```

into a direct lower bound for `loss(x,u)` on the same local source filter.

## Pen-And-Paper Calculation

Assume `0 < c`, `0 < c0`, and, eventually for `x` in the local source and for
regular coordinates `u` in the ball,

```text
c * A(x,u) <= B(x,u),
c0 * B(x,u) <= L(x,u),
```

where

```text
A(x,u) = residualSquareSum(x) + regularSquareSum(u).
```

Multiplying the first inequality by the nonnegative constant `c0` gives

```text
c0 * (c * A(x,u)) <= c0 * B(x,u).
```

By associativity of multiplication,

```text
(c0*c) * A(x,u) <= L(x,u).
```

Since `0 < c0*c`, this is exactly the loss lower-bound input required by the
local-source p.13 finite-integral theorem.  The residual positivity,
residual-power integrability, and density bounds are not changed; they remain
hypotheses over the supplied local source.

## Lean Landing

The landed theorem is in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_const_mul_adaptedProductDifferenceSquareSum_le_loss
```

It applies

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource
```

after forming the product constant `c0*c`.

## Remaining Boundary

This theorem does not prove the adapted product-coordinate lower bound, the
adapted-to-original loss comparison, local chart construction, source coverage,
density/Jacobian transport, normal crossings, pole order, or RLCT extraction.
