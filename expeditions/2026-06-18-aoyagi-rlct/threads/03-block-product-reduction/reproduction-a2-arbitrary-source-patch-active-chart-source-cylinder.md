# A2 Arbitrary Source Patch Active Chart Source Cylinder

Date: 2026-07-03.

## Local calculation

For the enlarged Case 2 source write the coordinates as

```text
z : (PassiveFields x CenterCoords) x FollowingFactor.
```

The unweighted source reference is

```text
unweightedSource =
  ((passiveRef.prod signedBoxMeasure).prod followingRef),
```

where

```text
signedBoxMeasure =
  Measure.pi (fun i => volume.restrict (-Rres i, Rres i)).
```

The finite-product signed-box calculation gives

```text
signedBoxMeasure = volume.restrict signedBox,
signedBox = signedBoxSet Rres.
```

Thus

```text
unweightedSource
  =
((passiveRef.prod (volume.restrict signedBox)).prod followingRef).
```

Using product restriction twice,

```text
passiveRef.prod (volume.restrict signedBox)
  =
(passiveRef.prod volume).restrict (univ x signedBox),
```

and

```text
((passiveRef.prod volume).restrict (univ x signedBox)).prod followingRef
  =
activeFull.restrict ((univ x signedBox) x univ).
```

In the nested source coordinates this cylinder is exactly

```text
sourceCylinder = {z | z.1.yNext in signedBox}.
```

So the unweighted source is the full active-coordinate additive Haar measure
restricted to `sourceCylinder`.

For an arbitrary measurable source patch `Omega`, the actual reference source
has the selected-entry density:

```text
referenceSource = unweightedSource.withDensity selectedEntryDensity.
```

Therefore

```text
referenceSource.restrict Omega
  =
((activeFull.restrict sourceCylinder).restrict Omega)
  .withDensity selectedEntryDensity
  =
(activeFull.restrict (Omega inter sourceCylinder))
  .withDensity selectedEntryDensity.
```

On any patch contained in the nonzero-pivot locus, the source-side
selected-entry chart change-of-variables theorem applies to
`Omega inter sourceCylinder`:

```text
map activeChart
  ((activeFull.restrict (Omega inter sourceCylinder))
    .withDensity selectedEntryDensity)
  =
activeFull.restrict (activeChart '' (Omega inter sourceCylinder)).
```

Combining the displayed equalities gives the arbitrary-source-patch bridge:

```text
map activeChart (referenceSource.restrict Omega)
  =
activeFull.restrict (activeChart '' (Omega inter sourceCylinder)).
```

The intersection with `sourceCylinder` is essential.  The named
`referenceSource` is supported on the original signed box before the active
selected-entry chart, so an arbitrary `Omega` cannot be pushed as if it carried
unrestricted full active Haar measure.

## Boundary

This layer is only source-side product bookkeeping plus the already proved
selected-entry source COV on the nonzero-pivot locus.  It does not prove a
scalar `1`, endpoint determinant-Haar identity, endpoint raw-Haar transport,
image-set matching with a determinant or p.13 patch, source-image coverage,
original-prior transport, normal crossings, pole order, or RLCT extraction.
