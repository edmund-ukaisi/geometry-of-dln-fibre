# Statement Card - A2 Source-Image Full Product Domination Handoff

## Claim

The source-image Jacobian finite-integral theorem is stable under finite-scalar
domination on the full p.13 product coordinate space.

Public Lean name:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalProductMeasure_le_smul_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Inputs Used

- the previous source-image finite-integral consumer;
- the same source-image density assumptions on
  `Measure.map sourceChart (baseJ.restrict W)`;
- source-stratum loss lower bound;
- finite domination
  `externalProductMeasure <= Cext • ((sourceImageMeasure.restrict
  (U ∩ sourceStratum)).prod ν)`;
- `Cext < ∞`.

## Output

For the returned open `U`, every externally supplied full product-coordinate
measure dominated by the source-image product measure has finite integral

```text
∫⁻ z, ofReal ((ball R).indicator
  (fun u => loss (z.1,u) ^ (-(t + regularCount/2))) z.2)
  ∂externalProductMeasure < ∞.
```

## Proof Shape

Apply the previous theorem with constant density `1`.  Then transfer the
finite lower integral to the external product measure by
`lintegral_lt_top_of_measure_le_smul`.

## Nonclaims

No original DLN prior is constructed.  No theorem says the original prior is
dominated by the chart-produced product measure.  No Haar/source-prior
transport, source-rank coverage, normal crossings, pole order, or RLCT
extraction is proved.
