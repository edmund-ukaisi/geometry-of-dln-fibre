# A2 Active Product Reference Full Haar Restriction

Date: 2026-07-03.

## Local calculation

The matrix-entry reference measure is the finite product of one-dimensional
Lebesgue measures over the entries:

```text
matrixEntryReferenceMeasure m n =
  Measure.pi (fun _ : m => Measure.pi (fun _ : n => volume)).
```

For finite entry sets this is additive Haar because each one-dimensional
factor is additive Haar and finite products of additive Haar measures are
additive Haar.  The same calculation applies to the nested passive-field
reference measure: it is the product of the `A1`, `F2`, `A3`, `Ctop`, and `F3`
coordinate-product blocks, each of which is a finite matrix-entry product.

For the enlarged Case 2 source with the independent following factor, define
the full active-coordinate product reference

```text
activeFull =
  ((passiveRef.prod (volume : Measure CenterCoords)).prod followingRef).
```

Here `passiveRef` is the passive-field coordinate-product reference measure,
`CenterCoords` is the selected-entry center-coordinate function type, and
`followingRef` is the matrix-entry reference measure on the following factor.
Since the three factors are additive Haar and the product coordinate spaces
have measurable additive translations, `activeFull` is additive Haar.

The selected-entry active chart change of variables does not produce
`activeFull` itself.  It produces the restricted center-factor product

```text
((passiveRef.prod ((volume : Measure CenterCoords).restrict activeImage)).prod
  followingRef),
```

where

```text
activeImage =
  chartMap pivotNext '' signedBoxSet Rres.
```

The product-measure bookkeeping is:

```text
passiveRef.prod (volume.restrict activeImage)
  =
(passiveRef.prod volume).restrict (univ x activeImage),
```

and then, after taking the product with the following-factor measure,

```text
((passiveRef.prod (volume.restrict activeImage)).prod followingRef)
  =
activeFull.restrict ((univ x activeImage) x univ).
```

Under the nested coordinate shape

```text
z : (PassiveFields x CenterCoords) x FollowingFactor,
```

the cylinder `((univ x activeImage) x univ)` is exactly

```text
{ z | z.1.yNext in activeImage }.
```

This proves that the selected-entry active product reference is a restriction
of a full additive Haar product reference, not an additive Haar measure on the
whole active source.

## Boundary

This layer is only finite-coordinate Haar/product bookkeeping.  It does not
normalize a Haar scalar to `1`, does not identify an endpoint reference image,
does not prove determinant-Haar or raw-Haar transport, does not match the
active image set with a p.13 determinant patch, does not prove source-image
coverage or original-prior transport, and does not touch normal crossings,
pole order, or RLCT extraction.
