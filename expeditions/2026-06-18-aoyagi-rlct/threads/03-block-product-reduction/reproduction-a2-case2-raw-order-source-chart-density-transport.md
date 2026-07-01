# Reproduction - A2 Case 2 raw-order source-chart density transport

Date: 2026-07-01.

Status: pen-and-paper check for the conditional raw-order/source-chart density
transport bridge.

## Question

On the local Case 2 passive-theta sector, suppose `rawMap` sends theta
coordinates to the retained-passive raw-order p.13 tuple and `rawChart` is the
p.13 raw-order source chart.  If `sourceChart` is the direct concrete
passive-theta endpoint source chart, how should a raw density on

```text
Measure.map rawMap (thetaReference.restrict V)
```

compare with the composed theta-domain density?

## Calculation

The existing relative raw-order wrapper supplies an open shrink `V` such that

```text
rawChart (rawMap theta) = sourceChart theta
```

for every `theta ∈ V`.  It also supplies the two-stage measure equality for
any source measure restricted to `V`:

```text
Measure.map rawChart (Measure.map rawMap (sourceMeasure.restrict V))
=
Measure.map sourceChart (sourceMeasure.restrict V).
```

Apply this with the weighted theta measure

```text
sourceMeasure =
  thetaReference.withDensity
    (fun theta => rawDensity (rawMap theta)).
```

The right side is already the desired direct source-chart measure:

```text
Measure.map sourceChart
  ((thetaReference.withDensity
    (fun theta => rawDensity (rawMap theta))).restrict V).
```

On the left, use the elementary `withDensity` pushforward identity:

```text
Measure.map rawMap
  ((thetaReference.restrict V).withDensity
    (fun theta => rawDensity (rawMap theta)))
=
(Measure.map rawMap (thetaReference.restrict V)).withDensity rawDensity.
```

The rewrite `restrict_withDensity` identifies

```text
(thetaReference.withDensity
  (fun theta => rawDensity (rawMap theta))).restrict V
```

with the weighted restricted theta measure.  Therefore the raw-order
presentation equals the direct source-chart presentation:

```text
Measure.map rawChart
  ((Measure.map rawMap (thetaReference.restrict V)).withDensity rawDensity)
=
Measure.map sourceChart
  ((thetaReference.withDensity
    (fun theta => rawDensity (rawMap theta))).restrict V).
```

## Lean Target

Add the generic measure helper to
`lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`:

```text
measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict
```

and the concrete Case 2 wrapper to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
exists_open_subset_measure_map_case2PassiveThetaEndpoint_rawOrderSourceChart_withDensity_eq_sourceChart_withDensity
```

## Boundary

The calculation is conditional measure bookkeeping.  It keeps the raw/Haar
transport problem outside the theorem: no claim is made that the `rawMap`
pushforward is a raw Haar restriction, an original prior, or an original
volume.  It also does not prove source-image coverage, source-rank coverage,
normal crossings, pole order, or RLCT extraction.
