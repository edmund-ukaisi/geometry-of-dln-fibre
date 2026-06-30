# Reproduction - A2 passive-theta source-image measurability

Date: 2026-06-30.

## Goal

Record the source-side image-measurability step for the concrete Case 2
passive-theta endpoint chart.

The theorem should not prove source-rank coverage, source-image equality,
or source-prior transport.  It should only say that after shrinking the
theta domain, the actual fixed-base source-chart image is a measurable set,
and the already constructed source readback is a left inverse on that
shrink.

## Calculation

Let `theta` denote the full passive-theta coordinate:

```text
theta = (A1passive, F2, A3passive, Ctop, F3, yNext).
```

Let

```text
sourceChart(theta)
```

be the fixed-base p.13 source edge-family constructed from the
endpoint-transported retained-passive data, and let

```text
readback(E)
```

be the source-side readback that first applies retained-passive
`sourceReadback` to the fixed-base edge matrices and then applies the
selected-entry inverse readout to recover `yNext`.

The existing local inverse theorem gives an open neighborhood `Vread` of the
base point such that

```text
readback(sourceChart(theta)) = theta
```

for all `theta in Vread`.  Hence `sourceChart` is injective on any smaller
set `V subset Vread`: if `sourceChart(theta) = sourceChart(theta')`, applying
`readback` gives `theta = theta'`.

For measurability, shrink once more to the determinant-chart preimage:

```text
D = {theta | topologyTuple(retainedData(theta)) is in detChart}.
```

This set is open because `theta -> topologyTuple(retainedData(theta))` is
continuous and the retained-passive determinant chart is open.  On `D`,
`retainedData(theta)` lies in the determinant-chart subtype, so the source
chart is the composition

```text
theta |-> retainedData(theta)
      |-> determinant-chart subtype
      |-> fixed-base retained-passive p.13 source chart.
```

The last map is continuous by the existing retained-passive source-chart
continuity theorem.  Therefore `sourceChart` is continuous on

```text
V = G inter Vread inter D
```

for any prescribed open neighborhood `G` of the base point.

Since `V` is open, it is measurable.  The domain is Polish/Borel and the
target source edge-family space is open-measurable and T2, so the
Lusin-Souslin image theorem applies to the continuous injective restriction:

```text
MeasurableSet (sourceChart '' V).
```

## Boundary

This is a local chart-image measurability theorem.  It does not say that all
nearby source-rank points lie in this image, does not compare the image with
an original DLN parameter prior, and does not identify determinant-chart Haar
measure.  It supplies a measurable source-side chart image for later
source-prior or coverage work.
