# Statement Card - A2 passive-theta source-image carrier and support

Date: 2026-06-30.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Expected public names:

```text
measure_map_restrict_image_eq_self_of_aemeasurable
exists_open_subset_continuousOn_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse
exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_rightInverse
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_restrict_image_eq_self_readback_leftInverse
```

Expected output:

```text
Given:
  z0 in determinant sector
  selected pivot nonzero at z0
  G open and z0 in G

Produce:
  open V
  z0 in V
  V subset G
  forall z in V, readback (sourceChart z) = z
  Set.InjOn sourceChart V
  ContinuousOn sourceChart V
  MeasurableSet (sourceChart '' V)
  forall E in sourceChart '' V:
    readback E in V
    sourceChart (readback E) = E
  for every thetaMeasure:
    (Measure.map sourceChart (thetaMeasure.restrict V)).restrict
      (sourceChart '' V)
    = Measure.map sourceChart (thetaMeasure.restrict V)
```

## Inputs Used

- `exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse`.
- The same determinant-chart continuity factorisation used in the source-image theorem, now exposed through a stronger local theorem with `ContinuousOn sourceChart V`.
- `ContinuousOn.aemeasurable` or `ContinuousOn.aemeasurable0` for the restricted measure.
- `ae_restrict_mem`.
- `ae_map_iff`.
- `Measure.restrict_eq_self_of_ae_mem`.

## Mathematical Meaning

The theorem says that the chart-produced pushed-forward measure lives on the
actual local source-chart image, and that `readback` is the inverse on that
named image.  This is the source-side analogue of the existing endpoint-sector
support theorem, but it is still only support on the named image.

## Nonclaims

- No source-rank local coverage.
- No equality between `sourceChart '' V` and any source-rank stratum.
- No original source-prior domination, equality, or transport.
- No determinant-chart Haar or raw-order Haar transport.
- No normal crossings, pole order, or RLCT extraction.
