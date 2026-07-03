# A2 with-following raw patch domination from active containment

Date: 2026-07-03.

## Claim

In the enlarged with-following Case 2 chart, after an internal proof shrink
around a determinant-sector basepoint with nonzero selected pivot, the following
input replaces a caller-supplied endpoint scalar for a raw-order patch
`P subset rawSourceSet`:

```text
rawDetChart inter rawOrderOnEndpoint^{-1}(P)
  subset activeWriteback '' (activeChart '' (V inter sourceCylinder)).
```

The remaining side conditions are still explicit: the endpoint patch
`rawDetChart inter rawOrderOnEndpoint^{-1}(P)` must be null-measurable for
`rawHaar`, the coordinate-source density must have a lower bound `epsilon` on
`baseJ.restrict V`, and `epsilon` must be neither `0` nor `infinity`.  The
scalar is not supplied by the caller.  It is the finite active-Haar scalar
obtained from the active endpoint reference-image theorem.

## Pen-and-paper chain

Fix the local raw patch

```text
endpointPatch := rawDetChart inter rawOrderOnEndpoint^{-1}(P).
```

First shrink the requested neighborhood `G` by the selected-pivot-nonzero open
set inside the proof.  Since the base point already has nonzero pivot, the
shrink is nonempty at the base point.  The existing localized source-density
theorem applied to this smaller neighborhood returns an open `V` with

```text
V subset G,
V subset {z | selected pivot of z is nonzero}.
```

For this same `V`, the active endpoint theorem applies with `Omega := V`.  The
explicit containment hypothesis gives

```text
endpointPatch subset activeWriteback '' (activeChart '' (V inter sourceCylinder)).
```

The active endpoint theorem then produces a finite scalar `Cdet` such that

```text
rawHaar.restrict endpointPatch
  <= Cdet * case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure(V).
```

By definition, the named endpoint reference image is

```text
case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure(V)
  = Measure.map Y (referenceSource.restrict V).
```

Thus we have exactly the endpoint-patch domination hypothesis consumed by the
existing localized source-density handoff.

Finally, if the coordinate-source density has lower bound `epsilon` on
`baseJ.restrict V`, the lower-density handoff gives

```text
rawHaar.restrict P
  <= (Cdet * epsilon^{-1}) *
       Measure.map rawMap (coordinateSourceMeasure.restrict V),
```

and `Cdet * epsilon^{-1} < infinity` follows from `Cdet < infinity`,
`epsilon != 0`, and `epsilon != infinity`.

## Boundary

This is a local raw-patch domination theorem.  It does not prove exact
raw-Haar pushforward, raw-Haar normalization, determinant-chart Haar transport,
global source coverage, source-rank coverage, finite atlas coverage, endpoint
patch null-measurability, source-density positivity, normal crossings, pole
order, or RLCT extraction.
