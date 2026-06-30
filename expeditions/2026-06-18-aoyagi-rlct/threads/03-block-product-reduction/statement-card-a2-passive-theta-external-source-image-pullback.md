# Statement Card - A2 passive-theta external source-image pullback

Date: 2026-06-30.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Public generic names:

```text
measure_map_rightInverse_restrict_image_eq_self_of_aemeasurable
measure_map_readback_restrict_image_restrict_eq_self_of_aemeasurable
aemeasurable_of_continuousOn_of_measure_restrict_eq_self
```

Concrete name:

```text
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_restrict_image_eq_self
```

## Expected Output

After shrinking inside a prescribed open theta-neighborhood `G`, obtain an
open `V` with:

```text
z0 in V
V subset G
forall z in V, readback (sourceChart z) = z
Set.InjOn sourceChart V
ContinuousOn sourceChart V
MeasurableSet (sourceChart '' V)
```

and for every external source-side measure `externalMeasure`, if

```text
readback is AEMeasurable for
  externalMeasure.restrict (sourceChart '' V),
```

then, with

```text
candidateMeasure =
  Measure.map readback (externalMeasure.restrict (sourceChart '' V)),
```

prove:

```text
candidateMeasure.restrict V = candidateMeasure
Measure.map sourceChart candidateMeasure =
  externalMeasure.restrict (sourceChart '' V)
```

The theorem deliberately stops before the domination pushforward:

```text
candidateMeasure ≤ c • baseJ.restrict V
```

to

```text
externalMeasure.restrict (sourceChart '' V) ≤
  c • Measure.map sourceChart (baseJ.restrict V).
```

That is the next conditional handoff once the right measurable-map API is
chosen for pushing inequalities.

## Inputs Used

- `exists_open_subset_continuousOn_measurableSet_case2PassiveThetaEndpointSourceChart_image_readback_leftInverse`
- `AEMeasurable.map_map_of_aemeasurable`
- `ae_map_iff`
- `Measure.map_congr`
- `Measure.restrict_eq_self_of_ae_mem`
- `ContinuousOn.aemeasurable`
- xhigh API scout `Huygens`, which confirmed the support-plus-pullback theorem
  shape and the need to assume `AEMeasurable readback` for the restricted
  external measure.

## Mathematical Meaning

This turns the local chart-image right inverse into a measure-theoretic
external-source handoff.  The theorem constructs the coordinate-domain measure
that represents the portion of an external source measure lying in the chosen
passive-theta chart image.

## Nonclaims

- No proof that the original source prior is supported in one chart image.
- No source-rank coverage or source-image equality with a source-rank stratum.
- No proof that the pulled-back candidate measure is dominated by the
  passive-theta Jacobian-weighted product measure.
- No pushforward of such a domination to the source image in this theorem.
- No determinant-chart Haar or raw-order Haar transport.
- No normal crossings, pole order, or RLCT extraction.
