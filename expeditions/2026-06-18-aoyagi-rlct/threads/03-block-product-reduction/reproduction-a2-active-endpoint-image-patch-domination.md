# A2 Active Endpoint Image Patch Domination

Date: 2026-07-03.

## Local Calculation

For a measurable source patch `Omega` in the selected nonzero-pivot locus, the
previous active-coordinate theorem gives

```text
endpointReferenceImage =
  c * rawHaar.restrict (activeWriteback '' activePatchImage),
```

where

```text
activePatchImage =
  activeChart '' (Omega inter sourceCylinder),
sourceCylinder = {z | z.1.yNext in signedBoxSet Rres}.
```

In Lean the scalar is the canonical Haar scalar

```text
c =
  (Measure.map activeWriteback activeFull).addHaarScalarFactor rawHaar,
```

which is an `NNReal`.  Haar uniqueness gives `0 < c`, so `c != 0` and the
generic scalar inversion lemma applies:

```text
rawHaar.restrict (activeWriteback '' activePatchImage)
  =
c^{-1} * endpointReferenceImage.
```

If an endpoint patch `endpointPatch` is contained in the active endpoint image,

```text
endpointPatch subset activeWriteback '' activePatchImage,
```

then restriction monotonicity gives

```text
rawHaar.restrict endpointPatch
  <= rawHaar.restrict (activeWriteback '' activePatchImage)
  =
c^{-1} * endpointReferenceImage.
```

The inverse scalar is finite because it is the coercion of an `NNReal`.

## Boundary

The containment of `endpointPatch` in the active endpoint image is an explicit
hypothesis.  No theorem identifies a determinant-chart patch, raw-order patch,
p.13 patch, or source-image set with this active endpoint image.  The scalar
is the inverse of the canonical active Haar normalization scalar; it is not
proved to be `1`.  There is no determinant-Haar identity, raw-Haar transport,
original-prior transport, source-image coverage, normal crossings, pole order,
or RLCT extraction.
