# Statement Card - A2 passive theta source-image automatic readback measurability

## Claim

For the local passive-theta source-chart image, readback a.e. measurability
for the chart-produced source-image reference follows from the local
continuous injective source chart and the pointwise left inverse.  Consequently
the concrete bounded-density source-image pullback theorem no longer needs a
caller-supplied readback a.e.-measurability hypothesis.

## Public Lean Names

```text
aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
measure_map_readback_restrict_image_withDensity_le_smul_of_ae_le_of_continuousOn_injOn
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_withDensity_restrict_image_le_smul_of_continuousOn_injOn
```

## Inputs Used

- `MeasurableSet V`;
- Polish/Borel structure on the theta domain and Borel/T2 target structure;
- `ContinuousOn sourceChart V`;
- `Set.InjOn sourceChart V`;
- pointwise left inverse `readback (sourceChart theta) = theta` on `V`;
- bounded source-image density hypothesis for the final domination theorem.

## Output

The generic measurability theorem proves

```text
AEMeasurable readback
  (Measure.map sourceChart (thetaReference.restrict V)).
```

The bounded-density corollary proves the same domination as the previous
socket without the explicit `AEMeasurable readback` input:

```text
Measure.map readback
  (((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
    .restrict (sourceChart '' V))
  <= c • thetaReference.restrict V.
```

The concrete passive-theta wrapper returns a local open `V` and supplies this
readback-measurability proof internally.

## Nonclaims

No proof that an original DLN source prior has this density, no source-rank
coverage, no source-image equality beyond the local chart image, no Haar
transport, no normal crossings, no pole order, and no RLCT extraction.
