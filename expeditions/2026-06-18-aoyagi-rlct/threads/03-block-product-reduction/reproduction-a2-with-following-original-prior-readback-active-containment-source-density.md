# A2 with-following original-prior readback from active containment

Date: 2026-07-03.

## Claim

The original-volume active-containment readback wrapper has a direct
original-prior analogue.  For a measurable chart piece in the local source
image, let

```text
P = rawSourceSet inter rawChart^{-1}(chartPiece),
endpointPatch = rawDetChart inter rawOrderOnEndpoint^{-1}(P).
```

If

```text
endpointPatch subset activeWriteback '' (activeChart '' (V inter sourceCylinder)),
epsilon <= sourceDensity almost everywhere on baseJ.restrict V,
epsilon != 0, infinity,
```

then the original-volume wrapper supplies a finite `Cdet` and the domination

```text
readback_*(originalVolume.restrict chartPiece)
  <= Dvol • coordinateSourceMeasure.restrict G,

Dvol = (cHaar^{-1}) * (Cdet * epsilon^{-1}).
```

If the original-prior density is bounded above by `Kprior` on the same chart
piece, then

```text
originalPrior.restrict chartPiece
  <= ofReal(Kprior) • originalVolume.restrict chartPiece.
```

The generic readback domination handoff therefore gives

```text
readback_*(originalPrior.restrict chartPiece)
  <= Cprior • coordinateSourceMeasure.restrict G,

Cprior = ofReal(Kprior) * Dvol.
```

## Pen-and-paper calculation

Start with the original-volume active-containment theorem on the same local
neighborhood `V`.  Its endpoint-patch null-measurability and raw/source
composition are internal.  The caller supplies only the active endpoint-image
containment and the a.e. source-density lower bound.

The theorem returns:

```text
Cdet < infinity,
Ddet = Cdet * epsilon^{-1} < infinity,
AEMeasurable readback (originalVolume.restrict chartPiece),
readback_*(originalVolume.restrict chartPiece)
  <= ((cHaar^{-1}) * Ddet) • coordinateSourceMeasure.restrict G.
```

Now set

```text
Dvol = (cHaar^{-1}) * Ddet.
```

Since `cHaar^{-1}` is an `NNReal` coerced to `ENNReal`, it is finite; hence
`Dvol < infinity`.

The original prior is a density with respect to original volume.  The local
prior-density upper bound says

```text
density(E) <= Kprior
```

for `originalVolume.restrict chartPiece`-almost every `E`.  The standard
bounded-density lemma gives

```text
originalPrior.restrict chartPiece
  <= ofReal(Kprior) • originalVolume.restrict chartPiece.
```

Applying the generic map domination transfer with

```text
sourceRef = originalVolume.restrict chartPiece,
mu = originalPrior.restrict chartPiece,
thetaRef = coordinateSourceMeasure.restrict G,
C = ofReal(Kprior),
Csource = Dvol
```

gives both a.e. measurability of `readback` for the original-prior restriction
and the final domination with scalar

```text
Cprior = ofReal(Kprior) * Dvol.
```

The scalar is finite because `ofReal(Kprior) < infinity` and `Dvol < infinity`.

## Boundary

This wrapper does not prove active containment, source-density positivity,
prior-density boundedness, C-one signed-box support, determinant-chart Haar
transport, exact raw-Haar pushforward, Haar normalization, source coverage,
source-rank coverage, original source-prior transport beyond the bounded
density comparison, normal crossings, pole order, finite-integral transfer, or
RLCT extraction.  Source-cylinder and C-one support variants should remain
separate wrappers layered on top of this theorem or on top of the
source-cylinder/C-one original-volume wrappers.
