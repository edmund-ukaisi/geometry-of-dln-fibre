# Review - A2 passive-theta external source-image pullback

Date: 2026-06-30.

Reviewers: xhigh API scout `Huygens`; xhigh source/scope scout `Linnaeus`.

## Verdict

PASS for the exact support-plus-pullback theorem.

## Checks

`Huygens` confirmed the feasible Lean shape:

```text
candidateMeasure =
  Measure.map readback (externalMeasure.restrict (sourceChart '' V))

candidateMeasure.restrict V = candidateMeasure
Measure.map sourceChart candidateMeasure =
  externalMeasure.restrict (sourceChart '' V)
```

under:

```text
MeasurableSet V
MeasurableSet (sourceChart '' V)
ContinuousOn sourceChart V
AEMeasurable readback (externalMeasure.restrict (sourceChart '' V))
forall E in sourceChart '' V,
  readback E in V and sourceChart (readback E) = E
```

The proof route is pure measure theory: first prove the pulled-back measure is
supported on `V`, then derive a.e. measurability of `sourceChart` for that
measure from `ContinuousOn sourceChart V`, and finally use
`AEMeasurable.map_map_of_aemeasurable`, `Measure.map_congr`, and
`Measure.map_id`.

`Linnaeus` confirmed the mathematical boundary.  Aoyagi assumes a smooth
compactly supported prior density positive at the true parameter, but current
Lean does not identify that prior with the chart-produced passive measure.
The present theorem is therefore only the local measurable chart-image adapter
for the portion of an external source measure already restricted to one
passive-theta image.

## Next Boundary

The next handoff should be conditional domination:

```text
candidateMeasure ≤ c • baseJ.restrict V
```

implying a source-image domination after pushing by `sourceChart`.  This was
not included here because it needs a clean measurable-map inequality API or a
separate a.e.-measurable pushforward monotonicity lemma.

## Nonclaims

No source-rank coverage, no proof that the original source prior is supported
in one chart image, no source-prior density domination, no Haar transport, no
normal crossings, no pole order, and no RLCT extraction.

