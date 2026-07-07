# A2 With-Following Original-Prior Source-Cylinder Handoff

Date: 2026-07-07.

## Target

Consume the original-volume source-cylinder domination theorem with a local
upper bound for the original prior density.

The intended Lean theorem takes a measurable chart piece satisfying

```text
chartPiece subset sourceChart '' (V inter sourceCylinder)
```

a lower source-density bound on the same theta shrink, and an a.e. upper bound
for the original prior density on `originalVolume.restrict chartPiece`.  It
then returns a finite scalar such that

```text
originalPrior.restrict chartPiece
  <= Cprior * Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

Here

```text
Ddet = Cdet * eps^-1
Dvol = ((cHaar^-1 : NNReal) : ENNReal) * Ddet
Cprior = ofReal Kprior * Dvol.
```

## Pen-And-Paper Reproduction

The previous source-cylinder original-volume handoff proves, on a local
shrink, that

```text
originalVolume.restrict chartPiece <= Dvol * sourceRef,
```

where

```text
sourceRef = Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

The original edge-family prior is defined by density against original volume:

```text
originalPrior = originalVolume.withDensity (fun E => ofReal (density E)).
```

Therefore an a.e. upper bound

```text
density E <= Kprior
```

on `originalVolume.restrict chartPiece` gives

```text
originalPrior.restrict chartPiece
  <= ofReal Kprior * originalVolume.restrict chartPiece.
```

Composing the two measure dominations gives

```text
originalPrior.restrict chartPiece
  <= (ofReal Kprior * Dvol) * sourceRef.
```

Finiteness of `Cprior` follows from finiteness of `Dvol` and
`ofReal Kprior < infinity`.

## Boundary

This is bounded-density bookkeeping over the p.13 source-cylinder chart-piece
domination.  It does not prove source-density positivity, prior-density
boundedness, source-prior identification, original-prior transport, readback
domination, finite-integral transfer, determinant-chart Haar transport, exact
raw-Haar pushforward, Haar-scalar normalization, source coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction.
