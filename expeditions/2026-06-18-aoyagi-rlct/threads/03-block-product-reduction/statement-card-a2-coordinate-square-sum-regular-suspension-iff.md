# Statement Card - A2 coordinate-square-sum regular-suspension iff

Date: 2026-06-29.

## Claim

The local square-model threshold-shift iff now has coordinate-square-sum and
residual-block-square-sum wrappers.  For a finite-dimensional real regular
coordinate space `E` with Borel measurable structure and a measure `nu`
satisfying `[SFinite nu] [nu.IsAddHaarMeasure]`, under

```text
AEMeasurable (fun x => aoyagiCoordinateSquareSum (b x)) mu,
R > 0,
aoyagiCoordinateSquareSum (b x) > 0 a.e.,
aoyagiCoordinateSquareSum (b x) <= R^2 a.e.,
t > 0,
```

the product lower integral

```text
int^-_(x,u) 1_{ball(0,R)}(u)
  ofReal((aoyagiCoordinateSquareSum (b x)+||u||^2)^(-(t+finrank(E)/2)))
```

is finite if and only if the residual lower integral

```text
int^-_x ofReal((aoyagiCoordinateSquareSum (b x))^(-t))
```

is finite.  The residual-block version is the same statement with
`b x = AoyagiResidualBlockCoordinateIndex.value (D x)`.

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

Main theorems:

```text
lintegral_ofReal_residual_power_lt_top_of_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
lintegral_ofReal_residual_power_lt_top_of_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
```

## Proof Ingredients

- The generic model iff in `RegularSuspensionIntegrability.lean`;
- substitution `a := fun x => aoyagiCoordinateSquareSum (b x)`;
- residual-block substitution through
  `AoyagiResidualBlockCoordinateIndex.value`.

No new analytic estimate is introduced here.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionSquareSumIntegrability
```

## Nonclaims

- No original-loss, density, Jacobian, source-prior, or chart-coverage theorem.
- No residual-integrability proof for Aoyagi's reduced chart.
- No pole-order, normal-crossing, or RLCT claim.
