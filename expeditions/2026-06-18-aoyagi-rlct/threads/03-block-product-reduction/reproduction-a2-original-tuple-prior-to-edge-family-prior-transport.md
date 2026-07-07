# A2 original tuple prior to edge-family prior transport

## Object-level calculation

Fix bases `b` for the vertices.  They give inverse maps between the original
matrix tuple space and the continuous edge-family space:

```text
T = tupleToEdgeFamily b,
T^{-1} = edgeFamilyMatrixTuple b.
```

For a measurable tuple-side set `S`, the existing volume transport says

```text
map T ((originalTupleVolume d).restrict S)
  =
(originalEdgeFamilyVolume b).restrict (T '' S).
```

Now take a tuple density `phi`.  On the restricted tuple-volume measure, assume
the weighted density

```text
A |-> ofReal (phi A)
```

is a.e. measurable.  The edge-family density is its pullback along the inverse
matrix-coordinate map:

```text
E |-> ofReal (phi (edgeFamilyMatrixTuple b E)).
```

Since `edgeFamilyMatrixTuple b (tupleToEdgeFamily b A) = A`, this edge-family
density composed with `T` is exactly the tuple density.  Therefore the generic
map-with-density lemma gives

```text
map T (((originalTupleVolume d).restrict S).withDensity (ofReal phi))
  =
(map T ((originalTupleVolume d).restrict S)).withDensity
  (fun E -> ofReal (phi (edgeFamilyMatrixTuple b E))).
```

Combining this with the restricted volume transport and rewriting both sides
as the named prior measures gives

```text
map T ((originalTuplePrior d phi).restrict S)
  =
(originalEdgeFamilyPrior b (phi o edgeFamilyMatrixTuple b)).restrict (T '' S).
```

## Lean artifact

The new declaration is:

```text
map_tupleToEdgeFamily_originalTuplePrior_restrict_eq_originalEdgeFamilyPrior_restrict_image
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyRawOrderMeasureBridge.lean
```

It builds on:

```text
map_tupleToEdgeFamily_originalTupleVolume_restrict_eq_originalEdgeFamilyVolume_restrict_image
measure_map_withDensity_comp_of_aemeasurable
edgeFamilyMatrixTuple_tupleToEdgeFamily
```

## Boundary

This is a genuine original-prior transport step, but only across the fixed
finite-dimensional tuple/edge-family coordinate equivalence.  It does not
identify an Aoyagi source-chart image measure, compute a retained-passive
Jacobian, prove determinant/raw Haar transport, construct the source density,
prove source-rank or atlas coverage, construct normal crossings, compute pole
order, or extract an RLCT.
