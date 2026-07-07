# A2 original coordinate prior to edge-family prior transport

## Object-level calculation

Let

```text
C = canonicalCoord(d)^{-1} : (RepCoord d -> R) -> Tuple(d)
T = tupleToEdgeFamily(b) : Tuple(d) -> EdgeFamily
```

For a measurable coordinate-side set `S`, the coordinate prior is

```text
originalCoordinatePrior(d, phi)
  = originalCoordinateVolume(d).withDensity (ofReal o phi).
```

The tuple prior with transported density is

```text
originalTuplePrior(d, fun A => phi(canonicalCoord(d,A))).
```

Since `canonicalCoord(d, C x) = x`, the coordinate-side density is exactly the
pullback of the tuple-side density along `C`:

```text
(ofReal o phi)(x)
  = ofReal(phi(canonicalCoord(d, C x))).
```

The reusable with-density pushforward lemma gives

```text
map C ((originalCoordinateVolume d).restrict S).withDensity(g o C)
  =
(map C ((originalCoordinateVolume d).restrict S)).withDensity(g),
```

where `g(A) = ofReal(phi(canonicalCoord d A))`.  The measurable-equivalence
restriction formula gives

```text
map C ((originalCoordinateVolume d).restrict S)
  =
(originalTupleVolume d).restrict (C '' S).
```

Combining these gives the restricted coordinate-to-tuple prior transport.
Composing with the existing restricted tuple-to-edge-family prior transport
gives the fixed-basis coordinate-to-edge-family prior transport, with edge
density

```text
E |-> phi(canonicalCoord(d, edgeFamilyMatrixTuple(b,E))).
```

## Lean target

The coordinate-to-tuple theorem is in:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalPrior.lean
```

with name:

```text
map_canonicalCoord_symm_originalCoordinatePrior_restrict_eq_originalTuplePrior_restrict_image
```

The coordinate-to-edge-family theorem is in:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyRawOrderMeasureBridge.lean
```

with name:

```text
map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_eq_originalEdgeFamilyPrior_restrict_image
```

## Boundary

This is finite-dimensional coordinate/tuple/fixed-basis edge-family prior
transport only.  It does not identify an Aoyagi source-chart image measure,
construct a source-image density, compute a retained-passive Jacobian,
normalize Haar scalars, prove determinant/raw Haar transport, prove
source-rank or atlas coverage, construct normal crossings, compute pole order,
or extract RLCT.
