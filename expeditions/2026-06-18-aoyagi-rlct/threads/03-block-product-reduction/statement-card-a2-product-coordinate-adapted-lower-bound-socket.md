# Statement Card - A2 product-coordinate adapted lower-bound socket

Date: 2026-06-25.

## Claim

Given explicit product-coordinate shape data for an independent regular fiber
variable `u`, plus uniform product-reduction certificate and triangular
multiplier bounds, the p.13 adapted product-difference square-sum is bounded
below by a positive constant times

```text
residualSquareSumBase(x) + squareSum(u)
```

on the source-rank filter and regular ball.

## Lean Artifact

Expected theorem:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_nhdsWithin_source
```

## Inputs Kept Explicit

- product-coordinate square-sum shape;
- positive regular radius;
- cleaned-to-literal p.13 square-sum comparison on the product family;
- product-reduction certificates on the product family;
- uniform triangular multiplier bound;
- positive multiplier bound.

## Nonclaims

No product chart, coordinate construction, source coverage, signed-box
pushforward, density/Jacobian transport, normal crossings, pole order, or RLCT
extraction is proved.

## Verification

Checked with:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

The repository-preferred `scripts/lb` wrapper could not be used in this
sandbox because access to the shared Lean slot files under
`/home/ubuntu/.lake-shared` was denied by the environment policy.

## Review

xhigh review found two low-severity fidelity issues.  The Lean statement was
updated to require `0 < Rmax`, preventing an empty-ball-only socket.  The note
and card were also corrected to say the theorem assumes the cleaned-to-literal
comparison directly; deriving it from `F2/F3` smallness remains a separate
product-family constructor obligation.
