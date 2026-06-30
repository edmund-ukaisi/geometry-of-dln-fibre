# Statement Card - A2 source-image external density automatic readback

## Claim

An external measure restricted to a local source-chart image pulls back to a
coordinate-domain measure dominated by the coordinate reference measure, once
it is identified as a bounded-density perturbation of the chart-produced
source-image measure.  The readback a.e. measurability input is generated from
a continuous injective local chart and a pointwise left inverse.

Public Lean name:

```text
measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity_of_continuousOn_injOn
```

## Inputs Used

- `MeasurableSet V` and `MeasurableSet (sourceChart '' V)`;
- `ContinuousOn sourceChart V`;
- `Set.InjOn sourceChart V`;
- `readback (sourceChart theta) = theta` on `V`;
- equality of the restricted external measure with a restricted
  `withDensity` perturbation of
  `Measure.map sourceChart (thetaReference.restrict V)`;
- a.e. upper bound `density <= c` for the chart-produced image reference
  restricted to the image.

## Output

```text
Measure.map readback (externalMeasure.restrict (sourceChart '' V))
  <= c • thetaReference.restrict V
```

## Proof Shape

Use the measurable-embedding readback lemma to obtain

```text
AEMeasurable readback
  (Measure.map sourceChart (thetaReference.restrict V)).
```

Then apply the existing external-measure bounded-density theorem
`measure_map_readback_restrict_image_le_smul_of_restrict_eq_withDensity`.

## Nonclaims

No original DLN prior is constructed.  No source-rank coverage, Haar transport,
normal crossings, pole order, or RLCT extraction is proved.
