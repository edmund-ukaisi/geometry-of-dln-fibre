# A2 with-following original-prior readback from source-cylinder and C-one support

Date: 2026-07-03.

## Claim

The original-volume source-cylinder and C-one readback wrappers have direct
original-prior analogues.  In both cases the measure calculation is the same
bounded-prior-density handoff used by the active-containment prior wrapper.

For source-cylinder support, the caller supplies

```text
MeasurableSet chartPiece,
chartPiece subset sourceChart '' (V inter sourceCylinder),
epsilon <= sourceDensity almost everywhere on baseJ.restrict V,
epsilon != 0, infinity,
```

where

```text
sourceCylinder = {z | z.1.yNext in signedBox}.
```

The source-cylinder original-volume wrapper returns a finite `Cdet` and

```text
readback_*(originalVolume.restrict chartPiece)
  <= Dvol • coordinateSourceMeasure.restrict G,

Dvol = (cHaar^{-1}) * (Cdet * epsilon^{-1}).
```

For C-one support, the caller instead supplies

```text
MeasurableSet chartPiece,
chartPiece subset sourceChart '' V,
forall E in chartPiece, cOneReadout E in signedBox,
```

and the C-one original-volume wrapper first converts these into
source-cylinder support before returning the same original-volume readback
domination.

In either variant, if the original-prior density is bounded above by `Kprior`
on the same chart piece, then

```text
originalPrior.restrict chartPiece
  <= ofReal(Kprior) • originalVolume.restrict chartPiece.
```

The generic readback domination handoff gives

```text
readback_*(originalPrior.restrict chartPiece)
  <= Cprior • coordinateSourceMeasure.restrict G,

Cprior = ofReal(Kprior) * Dvol.
```

## Pen-and-paper calculation

### Source-cylinder support

The source-cylinder original-volume theorem has already performed the
endpoint-patch containment calculation:

```text
chartPiece subset sourceChart '' (V inter sourceCylinder)
  ==> endpointPatch subset
        activeWriteback '' (activeChart '' (V inter sourceCylinder)).
```

It then applies the active-containment original-volume readback theorem and
returns:

```text
Cdet < infinity,
Ddet = Cdet * epsilon^{-1} < infinity,
AEMeasurable readback (originalVolume.restrict chartPiece),
readback_*(originalVolume.restrict chartPiece)
  <= ((cHaar^{-1}) * Ddet) • coordinateSourceMeasure.restrict G.
```

Set

```text
Dvol = (cHaar^{-1}) * Ddet.
```

Since `cHaar^{-1}` is an `NNReal` coerced to `ENNReal`, it is finite, so
`Dvol < infinity`.

The prior-density hypothesis says

```text
density(E) <= Kprior
```

for `originalVolume.restrict chartPiece`-almost every `E`.  The bounded-density
comparison gives

```text
originalPrior.restrict chartPiece
  <= ofReal(Kprior) • originalVolume.restrict chartPiece.
```

Applying the generic map-domination transfer with

```text
sourceRef = originalVolume.restrict chartPiece,
mu = originalPrior.restrict chartPiece,
thetaRef = coordinateSourceMeasure.restrict G,
C = ofReal(Kprior),
Csource = Dvol
```

gives a.e. measurability of `readback` for the prior restriction and the
domination with scalar

```text
Cprior = ofReal(Kprior) * Dvol.
```

This scalar is finite because `ofReal(Kprior) < infinity` and
`Dvol < infinity`.

### C-one support

The C-one original-volume theorem has already performed the support
conversion:

```text
chartPiece subset sourceChart '' V,
forall E in chartPiece, cOneReadout E in signedBox
  ==> chartPiece subset sourceChart '' (V inter sourceCylinder).
```

That support conversion uses only the local readback identity
`readback(sourceChart z) = z` on `V` and the fact that the C-one readout of
`sourceChart z` is the theta-side `yNext` coordinate.  Once the theorem has
converted to source-cylinder support, the scalar and prior-density handoff are
identical to the source-cylinder case.

## Boundary

These wrappers do not prove source-cylinder support, C-one signed-box support,
source-density positivity, prior-density boundedness, determinant-chart Haar
transport, exact raw-Haar pushforward, Haar normalization, source coverage,
source-rank coverage, original source-prior transport beyond the bounded
density comparison, finite-integral transfer, normal crossings, pole order, or
RLCT extraction.  They are measure-domination wrappers only.

## Kill conditions

- If `chartPiece` is not measurable, the bounded-prior comparison cannot be
  applied to `originalVolume.restrict chartPiece`, so the wrapper calculation
  does not go through.
- If source-cylinder support is replaced by plain
  `chartPiece subset sourceChart '' V`, the source-cylinder wrapper has no
  endpoint-containment input; the C-one wrapper needs the additional pointwise
  `cOneReadout` signed-box support to recover it.
- If the source-density lower bound fails on `baseJ.restrict V`, the
  `epsilon^{-1}` source-density handoff used by the volume wrapper is not
  available.
- If `epsilon = 0` or `epsilon = infinity`, the scalar finiteness statement for
  `Cdet * epsilon^{-1}` is not the one proved by the existing volume wrapper.
- If the original-prior density is not bounded above by `Kprior` almost
  everywhere with respect to `originalVolume.restrict chartPiece`, the
  comparison
  `originalPrior.restrict chartPiece <= ofReal(Kprior) • originalVolume.restrict chartPiece`
  is unavailable.
- If the original-volume wrapper returned domination by a measure other than
  `coordinateSourceMeasure.restrict G`, the final scalar and target measure in
  the prior handoff would have to be restated.
