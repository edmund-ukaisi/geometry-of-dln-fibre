# A2 with-following original-volume readback from active containment

Date: 2026-07-03.

## Claim

The same-shrink original-volume readback bridge can consume the concrete
active-containment raw-patch theorem directly.  For a measurable chart piece
inside the local source-chart image, set

```text
P := rawSourceSet inter rawChart^{-1}(chartPiece)
endpointPatch := rawDetChart inter rawOrderOnEndpoint^{-1}(P).
```

If the endpoint patch is contained in

```text
activeWriteback '' (activeChart '' (V inter sourceCylinder)),
```

and the coordinate-source density has lower bound `epsilon` on
`baseJ.restrict V`, then there is a finite scalar `Cdet` such that
original-volume readback of `chartPiece` is dominated by the coordinate source
measure, with scalar

```text
((cHaar^{-1}) * (Cdet * epsilon^{-1})).
```

## Pen-and-paper chain

First use the existing same-shrink original-volume readback bridge.  It
returns a neighborhood `Vrb` with the local source-chart facts and a transfer
principle:

```text
rawHaar.restrict P <= D * rawMap_*(thetaReference.restrict Vrb)
  ==> readback_*(originalVolume.restrict chartPiece)
      <= (cHaar^{-1} * D) * thetaReference.restrict G.
```

Then apply the active-containment raw-patch theorem inside `Vrb`.  It returns
an open `V subset Vrb`.  For the concrete patch

```text
P = rawSourceSet inter rawChart^{-1}(chartPiece),
```

we have `P subset rawSourceSet` by projection.  Since `chartPiece` is
measurable, the existing p.13 raw-order measurability lemma gives
null-measurability of `endpointPatch`.

The active-containment raw-patch theorem consumes:

```text
endpointPatch subset activeWriteback '' (activeChart '' (V inter sourceCylinder)),
epsilon <= sourceDensity almost everywhere on baseJ.restrict V,
epsilon != 0, infinity.
```

It produces `Cdet < infinity` and

```text
rawHaar.restrict P
  <= (Cdet * epsilon^{-1}) *
       rawMap_*(coordinateSourceMeasure.restrict V).
```

Because `V subset Vrb`, this is also a raw domination over
`(coordinateSourceMeasure.restrict V).restrict Vrb`, so it can be fed into the
same-shrink original-volume readback bridge with
`D = Cdet * epsilon^{-1}`.  The final measure is widened from restriction to
`V` to restriction to `G` using `V subset G`.

## Boundary

This theorem does not prove the active containment hypothesis from ordinary
chart-piece support.  It also does not prove endpoint-patch measurability
beyond the concrete p.13 chart-piece case, source-density positivity,
determinant-chart Haar transport, exact raw-Haar pushforward, Haar
normalization, source coverage, source-rank coverage, original source-prior
transport, normal crossings, pole order, or RLCT extraction.
