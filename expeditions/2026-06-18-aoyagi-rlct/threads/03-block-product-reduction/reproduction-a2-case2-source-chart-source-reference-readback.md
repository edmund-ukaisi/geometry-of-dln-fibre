# Reproduction - A2 Case 2 source-chart source-reference readback

Date: 2026-07-01.

Status: pen-and-paper check for the chart-produced source-reference readback
wrapper.

## Question

Given the local passive-theta endpoint source chart

```text
sourceChart : Theta -> EdgeFamily
readback : EdgeFamily -> Theta
```

on an open set `V`, if `readback (sourceChart theta) = theta` for every
`theta in V`, can the chart-produced source-image reference

```text
sourceRef = Measure.map sourceChart (thetaReference.restrict V)
```

be pulled back exactly to `thetaReference.restrict V`?

## Calculation

On the local set supplied by the existing source-chart image theorem, the
source chart is continuous on `V`, injective on `V`, and has the pointwise
left inverse

```text
readback (sourceChart theta) = theta   for theta in V.
```

Since the theta domain is Polish and the target edge-family space is Borel and
T2, the continuous injective map on the measurable set `V` gives readback
a.e.-measurability on the chart-produced source-image measure:

```text
AEMeasurable readback
  (Measure.map sourceChart (thetaReference.restrict V)).
```

The push-pull identity is then the measure calculation

```text
Measure.map readback (Measure.map sourceChart (thetaReference.restrict V))
  = Measure.map (fun theta => readback (sourceChart theta))
      (thetaReference.restrict V)
  = Measure.map id (thetaReference.restrict V)
  = thetaReference.restrict V.
```

The second equality uses `ae_restrict_mem`: almost every point of
`thetaReference.restrict V` lies in `V`, so the pointwise left inverse applies
almost everywhere.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_sourceReference_eq_self
```

It should wrap the existing local continuous/injective source-chart image
theorem and apply:

```text
aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse
measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable
```

## Boundary

This identifies only the chart-produced source reference
`Measure.map sourceChart (thetaReference.restrict V)`.  It does not identify
an original source prior, prove source-image coverage, prove a density bound,
transport Haar measure, establish normal crossings, compute pole order, or
extract an RLCT.
