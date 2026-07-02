# Reproduction - A2 Case 2 with-following raw-order source-chart density handoff

Date: 2026-07-02.

Status: with-following conditional raw-density handoff reproduced and
formalised.  This note does not claim determinant-chart Haar transport,
raw-order Haar transport, source-image coverage, a Jacobian formula, normal
crossings, pole order, or RLCT extraction.

## Source Boundary

Aoyagi's Case 2 selected-pivot calculation, PDF pp. 19-21, gives the enlarged
source coordinates: passive-theta fields, the selected-entry chart coordinate,
and an independent following factor.  The existing Lean raw-order bridge
already proves that after shrinking to a determinant-sector, nonzero-pivot open
set `V`, the raw-order p.13 source chart agrees pointwise with the enlarged
endpoint source chart:

```text
rawChart (rawMap z) = sourceChart z  for z in V.
```

It also proves the corresponding two-stage measure identity for every
source-domain measure:

```text
Measure.map rawChart (Measure.map rawMap (sourceMeasure.restrict V))
  =
Measure.map sourceChart (sourceMeasure.restrict V).
```

The present step packages the same identity after inserting a supplied raw
density.

## Calculation

Fix a theta-domain reference measure `thetaReference` and a raw density

```text
rawDensity : RawTuple -> ENNReal.
```

Assume the measurability needed for the generic handoff:

```text
AEMeasurable rawMap (thetaReference.restrict V)
AEMeasurable rawDensity
  (Measure.map rawMap (thetaReference.restrict V)).
```

Apply the existing two-stage raw/source identity to the weighted theta-domain
measure

```text
thetaReference.withDensity (fun theta => rawDensity (rawMap theta)).
```

This gives

```text
Measure.map rawChart
  (Measure.map rawMap
    ((thetaReference.withDensity
      (fun theta => rawDensity (rawMap theta))).restrict V))
=
Measure.map sourceChart
  ((thetaReference.withDensity
    (fun theta => rawDensity (rawMap theta))).restrict V).
```

The generic `measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict`
lemma rewrites the left side by first pushing `thetaReference.restrict V`
through `rawMap` and then applying `withDensity rawDensity`.  Therefore

```text
Measure.map rawChart
  ((Measure.map rawMap (thetaReference.restrict V)).withDensity rawDensity)
=
Measure.map sourceChart
  ((thetaReference.withDensity
    (fun theta => rawDensity (rawMap theta))).restrict V).
```

## Checks

- The raw density is arbitrary and supplied; no Jacobian density is constructed.
- The theorem is local to the shrink `V` produced by the existing with-following
  raw-order bridge.
- The theorem does not identify any endpoint image with determinant-chart Haar
  or raw-order Haar.
- The result is a pure handoff socket for later raw-image/Jacobian work.
