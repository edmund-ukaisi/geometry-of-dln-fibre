# Reproduction - A2 retained-passive chart-produced measure handoff

Date: 2026-06-26.

Status: pen-and-paper prerequisite for the chart-produced-measure local
integrability handoff in `RetainedPassiveLocalMeasure.lean`.

## Question

The retained-passive selected-entry handoff previously required an explicit
measure equality

```text
mu.restrict localSource = Measure.map sourceChart sourceMeasure.
```

The new fixed-base retained-passive chart package does not prove this equality
for an arbitrary source measure `mu`.  It does, however, allow the special case
where `mu` is already defined as the pushed-forward signed-box measure:

```text
sourceMeasure =
  signedBox.withDensity (fun y => ofReal (sourceDensity y))

mu = Measure.map sourceChart sourceMeasure.
```

In that special case the only remaining measure-theory obligation is that the
pushed-forward measure is supported on the retained-passive local source.

## Support Calculation

Let

```text
localSource =
  paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge.
```

Assume `localSource` is measurable and

```text
for a.e. y with respect to sourceMeasure,
  sourceChart y in localSource.
```

If `sourceChart` is a.e. measurable, then the map-a.e. theorem gives

```text
for a.e. x with respect to Measure.map sourceChart sourceMeasure,
  x in localSource.
```

Therefore

```text
(Measure.map sourceChart sourceMeasure).restrict localSource
  = Measure.map sourceChart sourceMeasure
```

by `Measure.restrict_eq_self_of_ae_mem`.

For the selected-entry signed-box source measure, the available
`hsourceChart` is a.e. measurability with respect to the product signed box.
The with-density source measure is absolutely continuous with respect to that
box, so a.e. measurability transfers by `AEMeasurable.mono_ac`.

## Handoff

The existing selected-entry retained-passive theorem can then be applied with

```text
mu = Measure.map sourceChart sourceMeasure
```

and the required `hmap` supplied by the support calculation above.  No
Jacobian theorem is used at this stage: the density in `sourceMeasure` is the
already supplied selected-entry signed-box density.

The source-readback residual-factor variant first uses the existing algebraic
readout theorem

```text
sourceReadback residualFactorProduct = selected-entry center matrix
```

to recover the selected-entry residual square-sum, then calls the
chart-produced selected-entry handoff.

## Boundary

This removes `hmap` only in the chart-produced case.  It does not identify an
external or original DLN source measure with this pushforward, does not prove
source-rank coverage, does not compute the Jacobian of an original source
coordinate change, does not transport a prior density, and does not prove
normal crossings, pole order, or RLCT extraction.
