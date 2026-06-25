# Statement Card - A2 p.13 regular-coordinate bounded-density adapter

## Statement

Let `sourceData` be fixed-base p.13 regular/residual coordinate source data.
Let `rho` be its p.13 regular block coordinate index and set
`E = EuclideanSpace R rho`.

Lean proves

```text
finrank_R(E) = aoyagiTheorem2RegularVariableCount N H r.
```

Suppose, for a product measure on residual base variables and regular
coordinates, that

```text
residualSquareSum(x) > 0 a.e.,
int^- x, ofReal(residualSquareSum(x)^(-t)) < infinity,
t > 0,
R > 0,
c > 0,
C >= 0.
```

Assume on the regular coordinate ball:

```text
c * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),
0 <= density(x,u),
density(x,u) <= C.
```

Then

```text
int^- (x,u), ofReal(1_{ball(0,R)}(u) *
  loss(x,u)^(-(t + aoyagiTheorem2RegularVariableCount N H r / 2)) *
  density(x,u)) < infinity.
```

Here the regular ball restricts only the Euclidean regular-coordinate fiber.
Any base/chart/source-stratum restriction must already be encoded in the base
measure and the supplied product-measure hypotheses.

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.regularCoordinateEuclidean_finrank_eq_regularVariableCount
PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top
```

## Dependencies

- p.13 source-data regular coordinate count;
- `finrank_euclideanSpace`;
- `EuclideanSpace.real_norm_sq_eq`;
- the generic bounded-density regular-square wrapper.

## Nonclaims

No p.13 analytic chart construction, source-filter to product-measure a.e.
handoff, original DLN loss comparison, lower-loss construction, Jacobian/prior
density transport, residual-base integrability proof, endpoint/divergence,
threshold equality, normal crossings, pole order, or RLCT extraction is
proved.
