# Reproduction - A2 chart-piece readback-domination handoff

Date: 2026-06-30.

## Claim

Let `sourceChart` be the Case 2 passive-theta endpoint source chart and
`readback` its source-chart readback.  The existing finite-integral socket
returns an open theta set `W`, an open source neighborhood `U`, and

```text
sourceLocal = U inter sourceStratum.
```

It proves finite loss-power integrability for product measures dominated by a
finite scalar multiple of

```text
(sourceImageMeasure.restrict sourceLocal).prod nu,
```

where

```text
sourceImageBase = Measure.map sourceChart (baseJ.restrict W)
sourceImageMeasure = sourceImageBase.withDensity sourceImageDensity.
```

Define the theta-side coordinate source measure

```text
coordinateSourceMeasure =
  baseJ.withDensity (fun z => sourceImageDensity (sourceChart z)).
```

For any measurable `chartPiece subset sourceLocal`, if

```text
forall E in chartPiece,
  readback E in W and sourceChart (readback E) = E,
```

and the pulled-back external source measure is dominated by the theta-side
coordinate source measure,

```text
Measure.map readback (externalSourceMeasure.restrict chartPiece)
  <= Cpull * coordinateSourceMeasure.restrict W,
```

with `Cpull < infinity`, then Lean proves finite loss-power integrability over

```text
(externalSourceMeasure.restrict chartPiece).prod nu.
```

## Pen-And-Paper Check

This is a measure handoff.  No new Aoyagi normal-crossing or RLCT extraction
is used.

Write

```text
thetaWeighted = coordinateSourceMeasure.restrict W.
candidate =
  Measure.map readback (externalSourceMeasure.restrict chartPiece).
```

The supplied domination is

```text
candidate <= Cpull * thetaWeighted.
```

Since `sourceChart` is a.e. measurable for `thetaWeighted`, the domination
also makes `sourceChart` a.e. measurable for `candidate`.  Mapping the
domination by `sourceChart` gives

```text
Measure.map sourceChart candidate
  <= Cpull * Measure.map sourceChart thetaWeighted.
```

The pointwise right-inverse hypothesis on `chartPiece` gives

```text
Measure.map sourceChart candidate =
  externalSourceMeasure.restrict chartPiece.
```

The chart-produced density identity gives

```text
Measure.map sourceChart thetaWeighted = sourceImageMeasure.
```

Therefore

```text
externalSourceMeasure.restrict chartPiece
  <= Cpull * sourceImageMeasure.
```

Because the left measure is restricted to `chartPiece` and
`chartPiece subset sourceLocal`, it is supported on `sourceLocal`.  The
domination sharpens to

```text
externalSourceMeasure.restrict chartPiece
  <= Cpull * sourceImageMeasure.restrict sourceLocal.
```

Producting with the fixed regular-coordinate Haar measure preserves this
finite-scalar domination, using `[SFinite nu]`:

```text
(externalSourceMeasure.restrict chartPiece).prod nu
  <= Cpull * (sourceImageMeasure.restrict sourceLocal).prod nu.
```

The existing finite-product socket then transfers finite integrability.

## Boundary

The theorem assumes the readback domination and the pointwise right-inverse
property on `chartPiece`.  It does not prove that a chart image equals
`sourceLocal`, does not prove source-rank coverage, and does not identify the
original DLN prior with `externalSourceMeasure`.  It also does not prove Haar
transport, normal crossings, pole order, or RLCT extraction.
