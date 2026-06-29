# Reproduction - A2 two-sided loss-density supplied comparison iff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised for supplied local comparison
hypotheses.

## Source Anchor

Aoyagi PDF p. 13 reduces the regular-coordinate layer to a square model

```text
q(x,u) = residualSquareSum(x) + regularSquareSum(u).
```

The previous checkpoints formalised the local threshold shift for this model.
The present step adds the elementary comparison layer: if an actual transported
loss and density are supplied to be uniformly comparable to the model on the
regular ball, then the actual loss-density lower integral has the same
finite-integrability threshold as the residual square-sum model.

This is not a proof that Aoyagi's original loss and prior density satisfy the
comparison hypotheses.  Those remain separate chart/transport inputs.

## Calculation

Let

```text
a(x) = aoyagiCoordinateSquareSum (b x),
q(x,u) = a(x) + ||u||^2,
s = t + finrank_R(E)/2.
```

Assume the model-iff hypotheses:

```text
AEMeasurable a mu,
0 < R,
a(x) > 0 a.e.,
a(x) <= R^2 a.e.,
0 < t,
[SFinite nu],
[nu.IsAddHaarMeasure].
```

On the product regular ball, suppose the supplied comparison constants satisfy

```text
0 < cL, 0 < CL, 0 < dρ, 0 <= Dρ,
cL * q(x,u) <= L(x,u),
L(x,u) <= CL * q(x,u),
dρ <= ρ(x,u),
ρ(x,u) <= Dρ.
```

The finite direction is the already formalised one-sided estimate:

```text
L^(-s) ρ <= Dρ * cL^(-s) * q^(-s).
```

Thus residual finite integrability implies actual loss-density finite
integrability.

For the reverse direction, the lower loss bound and `a(x)>0` give `q>0` and
hence `L>0` on the regular ball.  The upper loss bound gives

```text
(CL * q)^(-s) <= L^(-s),
```

because `-s <= 0`.  Therefore

```text
dρ * CL^(-s) * q^(-s) <= L^(-s) ρ.
```

The positive constant `dρ * CL^(-s)` can be cancelled in `ENNReal`, so finite
actual loss-density integrability implies finite model integrability.  The
model iff then gives finite residual `a^(-t)` integrability.

Combining the two directions yields

```text
actual loss-density integral finite
iff
residual square-sum t-power integral finite.
```

## Lean Shape

Lean formalises the coordinate-level reverse and iff in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

with:

```text
lintegral_ofReal_residual_power_lt_top_of_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_loss_pos_of_loss_le_const_mul_of_const_le_density
lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
```

It also provides residual-block and fixed-base p.13 wrappers:

```text
lintegral_ofReal_loss_rpow_neg_mul_density_residualBlockSquareSum_add_norm_sq_indicator_ball_prod_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_two_sided_bounds
```

The p.13 wrapper only rewrites the regular-coordinate count and the Euclidean
regular square-sum; it adds no new analytic content.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionSquareSumIntegrability
```

passed.

## Nonclaims

- No construction of Aoyagi's p.13 analytic chart.
- No proof of the supplied two-sided loss bounds.
- No source-prior, Jacobian, density, or product-measure transport theorem.
- No proof of residual measurability, positivity, boundedness, or
  integrability.
- No normal-crossing theorem, pole-order theorem, or RLCT extraction.
