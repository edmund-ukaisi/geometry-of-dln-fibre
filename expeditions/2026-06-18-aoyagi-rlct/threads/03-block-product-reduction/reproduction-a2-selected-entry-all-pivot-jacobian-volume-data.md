# Reproduction - A2 selected-entry all-pivot Jacobian/volume data

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before review.

## Question

The all-pivot selected-entry finite chart family already has shared universal
source/chart domains, source coverage, chart regularity, and unit regularity.
The one-pivot selected-entry chart has a chart-point product-measure pushforward
packaged as `SelectedEntryAnalyticJacobianVolumeData`.  Can we lift that
Jacobian/volume field chart-by-chart to the shared all-pivot context?

Answer: yes.  The all-pivot chart indexed by `c : Fin center.card` is
definitionally the one-pivot selected-entry chart at pivot `chartEquiv c`.
Therefore the one-pivot chart-point measure theorem applies independently to
each chart.

## Calculation

Fix a finite center, a nonempty witness `hcenter`, an enumeration

```text
chartEquiv : Fin center.card ≃ center,
```

and positive radii

```text
R : center -> R,   hR : forall i, 0 < R i.
```

For chart `c`, set

```text
pivot_c = chartEquiv c,
ChartPoint_c = FormalChartPoint pivot_c,
chartMeasure_c = chartPointProductMeasure pivot_c R,
density_c x = ofReal (chartPointDensity pivot_c x),
chartTarget_c = chartMap pivot_c '' signedBoxSet R.
```

The one-chart theorem gives

```text
Measure.map (formalChartMap pivot_c)
  ((chartPointProductMeasure pivot_c R).withDensity
    (fun x => ofReal (chartPointDensity pivot_c x)))
=
volume.restrict (chartMap pivot_c '' signedBoxSet R).
```

The all-pivot context has `chartDomain c = Set.univ`, so the
`SelectedEntryAnalyticJacobianVolumeData` field

```text
Measure.map (C.chartMap c)
  (((chartMeasure c).restrict (ctx.chartDomain c)).withDensity (density c))
=
sourceMeasure.restrict (chartTarget c)
```

is exactly the one-chart equality after simplifying `restrict Set.univ`.
The nonzero target-measure field is also the one-chart theorem
`volume_restrict_chartMap_image_signedBoxSet_ne_zero pivot_c hR`.

## Lean target

Add:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotJacobianVolumeData.lean
```

with:

```text
selectedEntryAllPivotAnalyticJacobianVolumeData
selectedEntryAllPivotAnalyticJacobianVolumeCompatible
```

## Source Fidelity

Aoyagi PDF pp. 15-22 support the selected-entry coordinate substitution and
Jacobian density for a chosen pivot.  The all-pivot package is expedition-built
finite bookkeeping: it applies the same one-pivot calculation to every pivot in
the finite chart family.

## Kill Conditions

- The all-pivot chart map is not definitionally the one-pivot `formalChartMap`
  at `chartEquiv c`.
- The shared all-pivot chart domain is not `Set.univ`.
- The one-pivot pushforward theorem cannot simplify through the all-pivot
  context fields.

## Nonclaims

This does not prove transition regularity between distinct selected-entry
pivots, source production, branch termination, source-prior transport,
determinant-chart Haar transport, a full supplied analytic atlas producer,
normal-crossing extraction, pole order, or RLCT.
