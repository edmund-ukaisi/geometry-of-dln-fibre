# Statement Card - A2 residual square-sum integrability socket

Date: 2026-06-25.

## Claim

Let `b : α -> η -> ℝ` be a finite real coordinate family and put

```text
a(x) = aoyagiCoordinateSquareSum (b x).
```

If

```text
a(x) > 0  for mu-a.e. x,
t > 0,
∫⁻ x, ENNReal.ofReal (a(x)^(-t)) dmu < infinity,
```

then the product lower integral of

```text
(a(x)+||u||^2)^(-(t+finrank_R(E)/2))
```

over `α x ball(0,ρ)` is finite.  The same conclusion is proved for

```text
a(x) =
aoyagiCoordinateSquareSum (AoyagiResidualBlockCoordinateIndex.value (D x)).
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
DLNFibre.DLN.Aoyagi.lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

## Proof Ingredients

- Coordinate square-sum definition:
  `aoyagiCoordinateSquareSum`;
- residual block coordinate map:
  `AoyagiResidualBlockCoordinateIndex.value`;
- residual-power threshold-shift bridge:
  `lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale`;
- finite-side corollary:
  `lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top`.

## Nonclaims

- No proof that Aoyagi's residual square-sum is a.e. positive.
- No proof of residual negative-power integrability.
- No theorem for a positive-measure zero set.
- No endpoint theorem, divergent-side theorem, or threshold equality.
- No bounded-density/prior theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT.
