# A2 selected-entry one-chart Jacobian/volume data

## Scope

This note records the finite selected-entry chart-point volume-form
pushforward and the one-chart `SelectedEntryAnalyticJacobianVolumeData` field
that it supports.

This is not a full analytic atlas producer.  It does not prove source
coverage, transition regularity, unit regularity beyond the existing finite
certificate units, source production, branch termination, normal-crossing
extraction, pole order, or RLCT.

The Aoyagi calculation is the selected-entry substitution

```text
x_p = u,
x_i = u r_i  for i != p.
```

The chart-point coordinates are `(u, r)`.

## Volume-form calculation

Let `E` be a finite center set and `p in E`.  The chart-point source box is

```text
(-R_p, R_p) x prod_{i in E \ {p}} (-R_i, R_i).
```

Lean names its product measure:

```text
chartPointProductMeasure pivot R.
```

The selected-entry Jacobian density in chart-point coordinates is

```text
chartPointDensity_p(u, r) = |u|^(#(E \ {p})).
```

The selected-entry chart map is

```text
formalChartMap_p(u, r)_p = u,
formalChartMap_p(u, r)_i = u r_i  for i != p.
```

The center-coordinate Jacobian theorem already proves

```text
map chartMap_p
  ((prod_i volume|(-R_i,R_i)).withDensity (ofReal sourceDensity_p))
= volume.restrict (chartMap_p '' signedBoxSet R).
```

The banked adapter theorem proves

```text
map chartPointAdapter
  ((prod_i volume|(-R_i,R_i)).withDensity (ofReal sourceDensity_p))
= (chartPointProductMeasure pivot R).withDensity
  (ofReal chartPointDensity_p).
```

Since

```text
formalChartMap_p (chartPointAdapter y) = chartMap_p y,
```

the chart-point volume-form pushforward is

```text
map formalChartMap_p
  ((chartPointProductMeasure pivot R).withDensity
    (ofReal chartPointDensity_p))
= volume.restrict (chartMap_p '' signedBoxSet R).
```

No positivity hypothesis on `R` is needed for this equality.  It is a measure
identity, and degenerate boxes are allowed.

## One-chart data field

To package this equality as `SelectedEntryAnalyticJacobianVolumeData`, choose:

```text
chart certificate = selectedEntryCenterSqFormalJacobianChartCertificate pivot,
sourceDomain     = univ,
chartDomain      = univ,
sourceMeasure    = volume,
chartMeasure     = chartPointProductMeasure pivot R,
density          = ofReal chartPointDensity_p,
chartTarget      = chartMap_p '' signedBoxSet R.
```

The target nonemptiness and nonzero restricted source measure fields require
positive radii:

```text
forall i, 0 < R_i.
```

They are supplied by the already-proved inner-box theorem
`chartMapTargetInnerBox_subset_chartMap_image_signedBoxSet` and the nonzero
target-measure theorem.

This data fills only the Jacobian/volume compatibility record for the single
selected-entry chart.  It does not prove that this one chart covers a
neighborhood, that chart transitions are regular, or that a branch recursion
produces a full source atlas.

## Lean names

The chart-point pushforward theorem is:

```text
map_formalChartMap_chartPointProductMeasure_withDensity_eq_restrict_image
```

The one-chart context and data constructors are:

```text
selectedEntryOneChartAnalyticAtlasContext
selectedEntryOneChartAnalyticJacobianVolumeData
```

## Kill conditions

- Kill if this is described as a full `SelectedEntrySuppliedAnalyticAtlasProducer`.
- Kill if this is described as source coverage, transition regularity, source
  production, or branch termination.
- Kill if this is described as original/source-prior transport, determinant
  chart Haar transport, retained-passive Jacobian control, source-rank
  coverage, normal-crossing extraction, pole order, or RLCT.
- Kill if the density is dropped or replaced by an unweighted product measure.
- Kill if target nonemptiness or nonzero restricted source measure is claimed
  without positive radii.
