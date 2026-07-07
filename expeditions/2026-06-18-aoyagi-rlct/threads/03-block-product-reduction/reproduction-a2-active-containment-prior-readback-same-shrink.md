# A2 active-containment prior readback same-shrink adapter

## Object-level calculation

The active-containment original-prior readback theorem already gives, for a
returned theta shrink `V`,

```text
map readback (originalPrior.restrict chartPiece)
  <= Cprior * coordinateSourceMeasure.restrict G,
```

under the explicit active endpoint-patch containment

```text
endpointPatch subset activeWriteback '' (activeChart '' (V cap sourceCylinder)),
```

together with source-density lower and prior-density upper bounds.

For downstream rank-cut residual arguments the target measure should be

```text
coordinateSourceMeasure.restrict V,
```

not the ambient input `G`.  This is support bookkeeping.  The same theorem
also returns

```text
chartPiece subset sourceChart '' V,
readback(sourceChart z) = z for z in V,
V subset G.
```

Thus every point in the image of
`originalPrior.restrict chartPiece` under `readback` lies in `V`: if
`E in chartPiece`, choose `z in V` with `E = sourceChart z`; then
`readback E = z`.  Therefore the pushforward measure is supported on `V`.
Scalar domination by `coordinateSourceMeasure.restrict G` sharpens to scalar
domination by `coordinateSourceMeasure.restrict V`.

The proof uses the existing generic support-sharpening lemma

```text
measure_map_restrict_source_subset_image_le_smul_restrict_of_le_smul_restrict_superset.
```

## Boundary

This proves only the same-shrink adapter for an already supplied active
endpoint-patch containment.  It does not prove the active containment,
source-density positivity, determinant-chart Haar transport, exact raw-Haar
pushforward, Haar normalization, source coverage, source-rank coverage,
original source-prior transport beyond bounded-density comparison, normal
crossings, pole order, or RLCT extraction.
