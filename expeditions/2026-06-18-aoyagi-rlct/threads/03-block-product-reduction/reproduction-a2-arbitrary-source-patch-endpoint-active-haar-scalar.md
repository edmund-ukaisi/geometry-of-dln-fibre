# A2 Arbitrary Source Patch Endpoint Active Haar Scalar

Date: 2026-07-03.

## Local calculation

For the enlarged Case 2 source let

```text
Y : source -> endpoint topology tuple
W : active source coordinates -> endpoint topology tuple
```

where `W` is the active writeback continuous linear equivalence.  The endpoint
map factors as

```text
Y = W o activeChart.
```

For an arbitrary source patch `Omega`, the named endpoint reference image is

```text
endpointReferenceImage =
  map W (map activeChart (referenceSource.restrict Omega)).
```

The preceding source-patch calculation gives, under `Omega` contained in the
nonzero-pivot locus,

```text
map activeChart (referenceSource.restrict Omega)
  =
activeFull.restrict activePatchImage,
```

where

```text
sourceCylinder = {z | z.1.yNext in signedBoxSet Rres}
activePatchImage = activeChart '' (Omega inter sourceCylinder).
```

Substitution gives

```text
endpointReferenceImage =
  map W (activeFull.restrict activePatchImage).
```

Since `activeFull` is additive Haar on active source coordinates and `W` is a
continuous linear equivalence, the active-writeback Haar transport theorem
gives a scalar `c` such that

```text
map W (activeFull.restrict activePatchImage)
  =
c * rawHaar.restrict (W '' activePatchImage).
```

Thus

```text
endpointReferenceImage =
c * rawHaar.restrict
  (W '' (activeChart '' (Omega inter sourceCylinder))).
```

The support still contains the original signed-box source support through
`Omega inter sourceCylinder`; no statement says that the endpoint image is a
determinant chart patch or a p.13 raw-order patch.

## Boundary

This is active-coordinate endpoint Haar transport only, up to an existential
Haar scalar.  It does not prove scalar `1`, determinant-Haar normalization,
raw-Haar transport, original-prior transport, source-image coverage, p.13
patch matching, normal crossings, pole order, or RLCT extraction.
