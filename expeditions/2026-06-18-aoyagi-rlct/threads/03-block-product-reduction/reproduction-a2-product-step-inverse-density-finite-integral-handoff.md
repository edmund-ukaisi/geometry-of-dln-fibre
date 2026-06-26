# Reproduction - A2 p.13 product-step inverse-density finite-integral handoff

Date: 2026-06-26.

Status: implemented and reviewed.  Lean names:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_continuousAt_selfBase
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_selfBase
```

## Question

The previous checkpoint identified the concrete p.13 left-endpoint raw-shaped
target tuple

```text
Y(x,u) = (Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x))
```

and proved that the chart-side inverse product-step Jacobian density is
continuous and positive after composition with `Y` at a centered self-base
point.

The next finite-side handoff is to use this concrete density factor in the
already-proved p.13 local finite-integral theorem, replacing an abstract
positive continuous `density`.

## Pen-and-Paper Check

For the p.13 product-step chart, the target raw-order tuple is read as

```text
(Ctop, D, F3, A1, F2, A3, C).
```

The inverse raw-coordinate formula sends a target tuple to

```text
(C1, D, F3old, A1, A2, A3, A4)
```

with

```text
C1     = Ctop * A1^{-1},
F3old  = F3 + D A3 Ctop^{-1},
A2     = -A1 F2,
A4     = C - A3 F2.
```

For the concrete p.13 tuple

```text
Y(x,u) = (Ctop(u), Dtail(x), F3(u), Ctop(u), F2(u), 0, C0(x)),
```

this gives

```text
Phi^{-1}(Y(x,u)) =
(I, Dtail(x), F3(u), Ctop(u), -Ctop(u) F2(u), 0, C0(x)).
```

Thus no determinant or inverse of `Dtail(x)` is introduced.  The determinant
chart still asks only for the two `Ctop(u)` blocks, and the inverse-density
factor is a positive continuous local density at `(x0,0)`.  The finite-integral
handoff uses only continuity and strict positivity, shrinking the neighborhood
to obtain the needed local nonnegativity and upper bound.

## Lean Handoff

The existing theorem

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_continuousAt_pos_density
```

already proves local finite integrability for any supplied density that is
continuous and positive at `(x0,0)`.  The new theorem specializes its `density`
argument to

```text
fun xu =>
  productReductionStepRawOrderInverseJacobianDensity
    (paperEndpointFixedBaseP13RawOrderTuple V Bv U0 hU0 CedgeBase xu).
```

The proof uses:

```text
continuousAt_paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_selfBase
paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center
```

The signed-box theorem then composes this concrete-density finite-integral
handoff with the already-existing residual signed-box source-measure
constructor.

## Boundary

This checkpoint removes only the abstract regular-fiber density factor from
two local finite-integral handoffs.  It does not prove source coverage, the
p.13 product chart image, a product-step pushforward identity, original DLN
source/prior transport, identification of the signed-box source density with
the inverse Jacobian density, normal crossings, pole order, or RLCT.
