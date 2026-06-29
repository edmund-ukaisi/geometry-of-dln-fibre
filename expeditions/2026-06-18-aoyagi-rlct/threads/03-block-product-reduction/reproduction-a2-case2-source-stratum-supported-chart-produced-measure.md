# A2 Case 2 source-stratum-supported chart-produced measure

## Question

The retained-passive source-stratum membership theorem is pointwise: for each
selected-entry coordinate vector `yNext`, the endpoint-transported Case 2
source family is in Aoyagi's source-shaped rank stratum when the intended
edge-rank equations are supplied.  The next local-measure question is whether
the selected-entry weighted signed-box pushforward measure is supported on
that same source stratum.

This is a support statement only.  It does not identify the source stratum
with the image of the selected-entry chart.

## Generic support calculation

Let `S` be the source-shaped rank stratum

```text
paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge.
```

When `Cedge` is continuous, `S` is measurable.  If

```text
sourceChart : beta -> alpha
```

is a.e. measurable for a measure `eta`, and

```text
sourceChart y in S
```

for `eta`-almost every `y`, then the mapped measure is supported on `S`:

```text
forall^ae x with respect to Measure.map sourceChart eta, x in S.
```

This is exactly the `ae_map_iff` transport of the a.e. membership statement
across an a.e. measurable map.  Since the map measure is a.e. supported on the
measurable set `S`, measure restriction does nothing:

```text
(Measure.map sourceChart eta).restrict S = Measure.map sourceChart eta.
```

The Lean theorem

```text
measure_map_restrict_sourceRankStratum_eq_self_of_ae_mem
```

packages only this support calculation.

## Case 2 selected-entry measure

For the continuing Case 2 selected-entry chart, take

```text
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2),
sourceMeasure =
  (Measure.pi (fun i : center => volume.restrict (-Rres i, Rres i))).withDensity
    (fun y => ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)),
sourceChart yNext =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W2 B2 U0 hU0
    ((case2PostPivotSelectedEntryRetainedPassiveData ... yNext eNext).endpointTransport e).
```

The chart is continuous by the existing endpoint-transported Case 2 source
regularity theorem, hence a.e. measurable for the unsigned signed-box measure.
The weighted source measure is absolutely continuous with respect to that
unsigned signed-box measure by `withDensity_absolutelyContinuous`, so
a.e. measurability transfers to `sourceMeasure`.

For every `yNext`, the previously landed pointwise membership theorem gives

```text
sourceChart yNext in sourceStratum
```

from the explicit rank data

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
r + rank(case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext) = rEdge 1.
```

The successor-rank hypothesis is deliberately uniform in `yNext`; the theorem
does not compute a numerical rank for that successor selected-entry matrix.

Therefore

```text
(Measure.map sourceChart sourceMeasure).restrict sourceStratum
  = Measure.map sourceChart sourceMeasure.
```

## Boundary

This slice proves support of one constructed chart-produced measure under
explicit rank hypotheses.  It does not prove local source-rank coverage,
selected-entry image equality, exact-rank openness, source-prior or Jacobian
transport, analytic atlas construction, normal crossings, pole order, or RLCT.
