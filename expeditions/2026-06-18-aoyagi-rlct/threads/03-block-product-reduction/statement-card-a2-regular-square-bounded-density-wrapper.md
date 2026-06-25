# Statement Card - A2 regular-square bounded-density wrapper

## Statement

Let `a(x)=aoyagiCoordinateSquareSum (b x)`.  Suppose

```text
a(x) > 0 a.e.,
int^- x, ofReal(a(x)^(-t)) < infinity,
t > 0.
```

If on the regular ball, a.e. for the product measure,

```text
c * (a(x)+||u||^2) <= loss(x,u),   c > 0,
0 <= density(x,u),
density(x,u) <= C,                 C >= 0,
```

Here the regular ball is only the fiber ball in the `E` variable.  Any
base/chart restriction is part of the chosen base measure `mu`.

then

```text
int^- (x,u), ofReal((ball(0,R).indicator
  (fun u => loss(x,u)^(-(t+dim(E)/2)) * density(x,u)) u)) < infinity.
```

## Lean Names

```text
lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
lintegral_ofReal_loss_rpow_neg_mul_density_residualBlockSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

## Dependencies

- `lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top`;
- real-power monotonicity for nonpositive exponents;
- bounded-density comparison `0 <= density <= C`;
- constant extraction for `ENNReal.ofReal`.

## Nonclaims

No p. 13 chart construction, original loss comparison, density/Jacobian
transport, residual-base integrability proof, endpoint/divergent-side theorem,
threshold equality, normal-crossing construction, pole order, or RLCT
extraction is proved.
