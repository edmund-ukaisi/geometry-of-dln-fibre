# Statement Card - A2 passive theta source-image Jacobian bridge

## Claim

A locally bounded density on the chart-produced passive-theta source-image base
feeds into the existing Jacobian-weighted residual-source theorem.  The result
is a source-image consumer: it proves support, residual positivity, and finite
negative-power integrability for

```text
(Measure.map sourceChart (baseJ.restrict W)).withDensity sourceImageDensity.
```

## Public Lean Name

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- finite passive measure and the selected-entry residual critical inequality;
- the existing Jacobian-weighted theta-domain bounded-density residual-source
  theorem;
- a density `sourceImageDensity : EdgeFamily -> ENNReal`;
- local a.e. measurability of `sourceChart` with respect to `baseJ.restrict W`;
- a.e. measurability of `sourceImageDensity` with respect to
  `Measure.map sourceChart (baseJ.restrict W)`;
- a finite a.e. upper bound for `sourceImageDensity` on that source-image base.

## Output

For a returned open `W` containing the theta base point, define

```text
sourceImageBase = Measure.map sourceChart (baseJ.restrict W)
sourceImageMeasure = sourceImageBase.withDensity sourceImageDensity
localSource = paperEndpointFixedBaseRetainedPassiveP13LocalSource ...
```

The theorem proves:

```text
sourceImageMeasure.restrict localSource = sourceImageMeasure
```

and

```text
0 < residual square-sum
```

for `sourceImageMeasure.restrict localSource`-a.e. source point, plus

```text
residualNegPowerIntegrableOn ... localSource sourceImageMeasure t.
```

The finite-integral theorem also proves the p.13 regular-coordinate local
finite-side conclusion:

```text
∫⁻ z, ofReal ((ball R).indicator
  (fun u => loss (z.1,u) ^ (-(t + regularCount/2)) * density (z.1,u)) z.2)
  ∂(sourceImageMeasure.restrict (U ∩ sourceStratum)).prod nu < ∞.
```

## Nonclaims

No proof that the original DLN prior has this density, no passive-theta-only
representation of the full p.13 source prior, no source-rank coverage, no Haar
transport, no determinant-chart/raw-order measure identity, no normal
crossings, no pole order, and no RLCT extraction.
