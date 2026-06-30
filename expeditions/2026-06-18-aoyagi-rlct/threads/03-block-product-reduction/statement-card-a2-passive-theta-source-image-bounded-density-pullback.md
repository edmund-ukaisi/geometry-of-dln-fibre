# Statement Card - A2 passive theta source-image bounded-density pullback

## Claim

For a local passive-theta source-chart image `sourceChart '' V`, a
bounded-density perturbation of the chart-produced source-image reference

```text
Measure.map sourceChart (thetaReference.restrict V)
```

pulls back by `readback` to a measure dominated by
`thetaReference.restrict V`.

## Public Lean Names

```text
measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le
measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_withDensity_restrict_image_le_smul
```

## Inputs Used

- local left inverse `readback (sourceChart theta) = theta` on `V`;
- `MeasurableSet V` and `MeasurableSet (sourceChart '' V)`;
- `AEMeasurable sourceChart (thetaReference.restrict V)`;
- `AEMeasurable readback (Measure.map sourceChart (thetaReference.restrict V))`;
- bounded source-image density hypothesis
  `density <= c` a.e. for the chart-produced source-image reference.

## Output

The generic density theorem proves

```text
Measure.map readback
  (((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
    .restrict (sourceChart '' V))
  <= c • thetaReference.restrict V.
```

The external-measure variant adds the explicit density identity

```text
externalMeasure.restrict (sourceChart '' V)
  =
  ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
    .restrict (sourceChart '' V)
```

and concludes the same domination for
`Measure.map readback (externalMeasure.restrict (sourceChart '' V))`.

## Nonclaims

No proof that an original DLN source prior has this density, no source-rank
coverage, no source-image equality beyond the local chart image, no Haar
transport, no normal crossings, no pole order, and no RLCT extraction.
