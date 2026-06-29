# Statement Card - A2 two-sided loss-density supplied comparison iff

Date: 2026-06-29.

## Claim

Under the model-iff hypotheses

```text
AEMeasurable residual square-sum,
0 < R,
residual square-sum > 0 a.e.,
residual square-sum <= R^2 a.e.,
0 < t,
[SFinite nu],
[nu.IsAddHaarMeasure],
0 < cL, 0 < CL, 0 < dρ, 0 <= Dρ,
```

and supplied local two-sided comparison bounds

```text
cL * model <= loss <= CL * model,
dρ <= density <= Dρ,
```

actual loss-density integrability on the regular ball is equivalent to
residual square-sum `t`-power integrability.  The model is

```text
model(x,u) = aoyagiCoordinateSquareSum (b x) + ||u||^2
```

at exponent `t + finrank(E)/2`.  The p.13 wrapper rewrites this to

```text
residualSquareSum(x) + regularCoordinateSquareSum(u)
```

at exponent

```text
t + aoyagiTheorem2RegularVariableCount N H r / 2.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

Main theorem names:

```text
lintegral_ofReal_residual_power_lt_top_of_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_loss_pos_of_loss_le_const_mul_of_const_le_density
lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
lintegral_ofReal_loss_rpow_neg_mul_density_residualBlockSquareSum_add_norm_sq_indicator_ball_prod_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
```

## Proof Ingredients

- The model square-sum threshold-shift iff;
- existing one-sided supplied lower-loss/upper-density finite theorem;
- new reverse comparison using `loss <= CL * model` and `dρ <= density`;
- ENNReal cancellation of the positive finite constant `dρ * CL^(-s)`.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionSquareSumIntegrability
```

## Nonclaims

- No actual proof of the comparison hypotheses.
- No p.13 chart construction or coverage theorem.
- No source-prior, Jacobian, density, or measure-transport theorem.
- No pole-order, normal-crossing, or RLCT claim.
