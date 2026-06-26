# Reproduction - A2 original-loss product-step inverse-density handoff

Date: 2026-06-26.

Status: finite-integral specialization; formalised; reviewed.

Statement card:
`statement-card-a2-original-loss-product-step-inverse-density-handoff.md`.

Review:
`review-a2-original-loss-product-step-inverse-density-handoff.md`.

## Purpose

The existing original-loss product-family theorem proves local finite
integrability for

```text
lossDLN(CedgeProd(x,u))^(-(t + regularCount/2)) * density(x,u)
```

under explicit hypotheses that the transported density factor is continuous
and positive at `(x0,0)`.

The p.13 product-step inverse-density work already proved those two hypotheses
for the concrete chart-side inverse Jacobian density

```text
delta(x,u) =
  productReductionStepRawOrderInverseJacobianDensity
    (paperEndpointFixedBaseP13RawOrderTuple V Bv U0 hU0 CedgeBase (x,u)).
```

This slice substitutes `delta` into the original-loss product-family theorem.

## Pen-and-Paper Check

Let

```text
Y(x,u) = paperEndpointFixedBaseP13RawOrderTuple V Bv U0 hU0 CedgeBase (x,u).
```

The previous p.13 product-step calculation proves:

```text
ContinuousAt (fun xu => productStepInverseJacobianDensity(Y xu)) (x0,0),
0 < productStepInverseJacobianDensity(Y(x0,0)).
```

The original-loss edge-matrix product-family theorem only requires these two
facts about the abstract factor `density`; all source-measure and residual
signed-box hypotheses are independent of the density's formula.  Therefore the
theorem applies with `density = delta`, giving the same output:

```text
exists R C U,
  0 < R, R <= Rmax, 0 <= C, IsOpen U, x0 in U,
  lintegral over (mu.restrict (U inter sourceStratum)).prod nu is finite.
```

The integrand is now the original square-Frobenius loss multiplied by the
concrete inverse product-step Jacobian density along the p.13 raw-order tuple.

## Lean Handoff

File:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalLossLocalMeasure.lean
```

New theorem:

```text
exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase
```

It calls:

```text
exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density
```

with the concrete `density` above, supplying continuity and positivity via:

```text
continuousAt_paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_selfBase
paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center
```

## Boundary

This is a local finite-integral specialization.  It does not construct the
p.13 product chart, prove source coverage, prove a product-step/source
pushforward, identify the signed-box density with the inverse Jacobian density,
transport the original DLN prior measure, produce normal crossings, compute
pole order, or extract RLCT.
