# A2 Endpoint Reference Image Univ Active Haar Scalar

Date: 2026-07-03.

## Local calculation

For the enlarged Case 2 with-following source, let

```text
Y : source -> endpoint topology tuple
```

be the endpoint topology-tuple map, and let

```text
W : active coordinates -> endpoint topology tuple
R : endpoint topology tuple -> active coordinates
```

be the active writeback/readout continuous linear equivalence.  The pointwise
coordinate calculation already proved that

```text
Y = W o activeChart,
```

where `activeChart` leaves the passive fields and following factor unchanged
and sends the selected-entry center coordinates through
`chartMap pivotNext`.

For the unrestricted source `Omega = Set.univ`, the named endpoint reference
image is therefore

```text
endpointReferenceImage
  = map W (map activeChart referenceSource).
```

The selected-entry source COV gives

```text
map activeChart referenceSource
  =
((passiveRef.prod (volume.restrict activeImage)).prod followingRef),
```

where

```text
activeImage = chartMap pivotNext '' signedBoxSet Rres.
```

The previous product-restriction layer identifies this product with

```text
activeFull.restrict activeCylinder,
```

where

```text
activeFull = ((passiveRef.prod volume).prod followingRef)
activeCylinder = {z | z.1.yNext in activeImage}.
```

Since `activeFull` is additive Haar and `W` is a continuous linear equivalence,
the active-writeback Haar transport theorem gives a scalar `c` such that

```text
map W (activeFull.restrict activeCylinder)
  =
c * rawHaar.restrict (W '' activeCylinder).
```

Composing the displayed equalities gives the new theorem:

```text
endpointReferenceImage
  =
c * rawHaar.restrict (W '' activeCylinder).
```

## Boundary

The source restriction is `Set.univ`.  This theorem does not rewrite an
arbitrary local source patch through the active chart.  The scalar is
existential and is not identified with `1`.  The endpoint set is only
`W '' activeCylinder`; it is not matched with a determinant-chart patch or a
p.13 raw-order patch.  No determinant-Haar weighted image identity, Jacobian
formula, raw-Haar transport, source-image coverage, original-prior transport,
normal crossings, pole order, or RLCT extraction is proved.
