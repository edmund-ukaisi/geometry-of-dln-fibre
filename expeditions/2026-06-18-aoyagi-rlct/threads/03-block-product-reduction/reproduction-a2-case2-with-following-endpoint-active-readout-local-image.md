# A2 Case 2 With-Following Endpoint Active Readout Local Image

## Purpose

This note records the elementary local-image calculation needed before trying
to lift the source-side selected-entry change of variables to an endpoint-side
localized Haar statement.  The point is deliberately modest: on the actual
endpoint image of a source patch where the selected pivot is nonzero, the
active endpoint readout is injective and its image is exactly the active
selected-entry source chart image.  This is not a determinant-Haar
identification and does not prove any raw-map pushforward.

## Paper Calculation

In Aoyagi Case 2, after choosing the successor pivot, the endpoint tuple keeps
the passive fields and replaces the successor center block by the
selected-entry chart coordinates.  In the with-following version there is one
extra following factor, carried unchanged as the other active `C` block.

For source coordinates

```text
z = ((passive fields, y_next), F_follow)
```

write

```text
Y(z) = case2PassiveThetaWithFollowingFactorEndpointTopologyTuple(z)
R(T) = endpointTopologyTupleActiveReadout(T).
```

The finite-coordinate readout calculation is

```text
R(Y(z)) = ((passive fields, chartMap(pivotNext)(y_next)), F_follow).
```

Thus for any source set `Omega`,

```text
R '' (Y '' Omega)
  = activeSelectedEntryChart '' Omega.
```

If `Omega` is contained in the nonzero-pivot locus, then the selected-entry
chart map is injective on the center coordinate by the elementary pivot
formula:

```text
chartMap_p(y)_p = y_p,
chartMap_p(y)_i = y_p y_i       for i != p.
```

Equality of active readouts therefore gives equality of passive fields,
following factors, and selected-entry charted centers.  Since the pivot
coordinate is nonzero on both source points, the center coordinates agree.
Hence the source points agree, and consequently the endpoint points agree.
So `R` is injective on `Y '' Omega`.

## Boundary

This supports a later localized endpoint COV theorem by isolating the precise
image on which the active readout can be used as a coordinate witness.  It does
not say that `Y '' Omega` is the full determinant chart, and it does not
replace determinant Haar by the endpoint reference image.
