# Reproduction - A2 Case 2 passive-reference determinant-chart transfer

Date: 2026-07-01.

Status: pen-and-paper reproduction for a passive-reference domination adapter.

## Question

Suppose a future concrete passive-field reference measure
`passiveReferenceMeasure` has already been compared with determinant-chart
Haar after taking the selected-entry product:

```text
Measure.map Y (passiveReferenceSource.restrict V)
  <= c • rawReference.restrict rawDetChart.
```

If an actual passive-field measure is dominated by that reference,

```text
passiveMeasure <= d • passiveReferenceMeasure,
```

what follows for

```text
passiveSource = passiveMeasure.prod weightedBox?
```

## Calculation

The selected-entry factor `weightedBox` is fixed on the right.  Left-factor
domination lifts to product measures:

```text
passiveMeasure.prod weightedBox
  <= d • passiveReferenceMeasure.prod weightedBox.
```

Restricting to the same theta-domain set `V` preserves the scalar domination:

```text
passiveSource.restrict V
  <= d • passiveReferenceSource.restrict V.
```

The endpoint topology-tuple map `Y` is continuous, hence a.e. measurable for
the reference restricted product source.  Mapping preserves the domination:

```text
Measure.map Y (passiveSource.restrict V)
  <= d • Measure.map Y (passiveReferenceSource.restrict V).
```

Composing with the supplied determinant-chart comparison for the reference
source gives

```text
Measure.map Y (passiveSource.restrict V)
  <= (d * c) • rawReference.restrict rawDetChart.
```

## Boundary

This is not a construction of the passive reference measure.  It also does
not prove the determinant-chart comparison for that reference.  It only says
that once such a reference comparison is proved, any passive-field measure
dominated by the reference inherits the comparison with the expected scalar
cost.

No exact raw-Haar pushforward, passive-product Haar transport, Haar
normalization, original source-prior transport, source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction is
proved here.
