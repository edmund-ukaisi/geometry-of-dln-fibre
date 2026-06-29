# Statement Card - A2 p.13 regular-coordinate model iff

Date: 2026-06-29.

## Claim

The fixed-base p.13 regular-coordinate square model now has an iff wrapper:

```text
product model integral finite
iff
residual square-sum t-power integral finite.
```

The product model is

```text
residualSquareSum(x) + regularCoordinateSquareSum(u)
```

on the regular ball, at exponent

```text
t + aoyagiTheorem2RegularVariableCount N H r / 2.
```

The theorem assumes the residual square-sum is a.e. measurable, positive
a.e., and bounded above by `R^2` a.e.; also `R>0`, `t>0`, and the regular
coordinate measure satisfies `[SFinite nu] [nu.IsAddHaarMeasure]`.

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

Theorem:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_p13RegularCoordinates_model_lt_top_iff_residual_power_lt_top
```

## Proof Ingredients

- Coordinate-square-sum model iff;
- p.13 regular-coordinate finrank/count identity from `sourceData`;
- Euclidean norm-square identity
  `||u||^2 = aoyagiCoordinateSquareSum (fun i => u i)`.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionSquareSumIntegrability
```

## Nonclaims

- No actual-loss, density, Jacobian, source-prior, or chart-coverage theorem.
- No proof of residual measurability, positivity, boundedness, or
  integrability.
- No pole-order, normal-crossing, or RLCT claim.
