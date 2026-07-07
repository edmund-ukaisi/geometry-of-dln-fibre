# A2 original coordinate prior edge-family preimage transport

## Object-level calculation

Let

```text
F(x) = tupleToEdgeFamily(b)((canonicalCoord d)^{-1}(x)).
```

The previous coordinate-to-edge-family theorem gives, for a measurable
coordinate-side set `S`,

```text
map F ((originalCoordinatePrior d phi).restrict S)
  =
originalEdgeFamilyPrior(b, E |-> phi(canonicalCoord d(edgeFamilyMatrixTuple b E)))
  restricted to F(S).
```

For downstream chart-piece use, take `S = F^{-1}(C)` for an edge-family set
`C`.  Since both `canonicalCoord^{-1}` and `tupleToEdgeFamily b` are
surjective equivalences onto the fixed-basis edge-family space,

```text
F(F^{-1}(C)) = C.
```

The only density measurability needed is the tuple-side one on the equivalent
restricted tuple set:

```text
originalTupleVolume d restricted to (tupleToEdgeFamily b)^{-1}(C).
```

The coordinate-volume restriction pushed through `canonicalCoord^{-1}` is
exactly this tuple restriction, because

```text
canonicalCoord^{-1}(F^{-1}(C)) = (tupleToEdgeFamily b)^{-1}(C).
```

Therefore the pushed restricted coordinate prior is exactly the restricted
edge-family prior on `C`.

## Lean target

The theorem lives in:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyRawOrderMeasureBridge.lean
```

with name:

```text
map_canonicalCoord_symm_tupleToEdgeFamily_originalCoordinatePrior_restrict_preimage_eq_originalEdgeFamilyPrior_restrict
```

## Boundary

This is a convenience form of finite-dimensional coordinate-to-edge-family
prior transport.  It does not identify an Aoyagi source-chart image measure,
construct a source-image density, compute a retained-passive Jacobian,
normalize Haar scalars, prove determinant/raw Haar transport, prove
source-rank or atlas coverage, construct normal crossings, compute pole order,
or extract RLCT.
