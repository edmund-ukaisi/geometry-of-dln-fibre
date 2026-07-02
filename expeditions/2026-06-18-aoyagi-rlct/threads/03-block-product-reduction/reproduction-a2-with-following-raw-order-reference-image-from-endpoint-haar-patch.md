# A2 With-Following Raw-Order Reference Image From Endpoint Haar Patch

## Purpose

The with-following endpoint reference image and raw-order reference image are
both named pushforwards of the same source-reference measure restricted to the
same local set `V`.  The endpoint image uses the endpoint topology tuple `Y`;
the raw-order image uses `Phi ∘ Y`, where `Phi = topologyTupleEdgeRawOrder`.

This checkpoint isolates the elementary measure consequence needed before the
localized reverse-domination package: if the endpoint image is a weighted Haar
patch on the determinant side, then the raw-order image is Haar restricted to
the corresponding raw-order image patch.

## Calculation

Let

```text
mu = referenceSource.restrict V
endpointReferenceImage = Measure.map Y mu
rawOrderReferenceImage = Measure.map (Phi ∘ Y) mu
J y = ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt y).
```

By map composition,

```text
rawOrderReferenceImage = Measure.map Phi endpointReferenceImage.
```

Assume a determinant-side patch `Omega` satisfies

```text
Omega subset topologyTupleDetChartSet
endpointReferenceImage = (rawHaar.restrict Omega).withDensity J.
```

The localized retained-passive raw-order COV then gives

```text
Measure.map Phi endpointReferenceImage
  = Measure.map Phi ((rawHaar.restrict Omega).withDensity J)
  = rawHaar.restrict (Phi '' Omega).
```

Therefore

```text
rawOrderReferenceImage = rawHaar.restrict (Phi '' Omega).
```

Any post-map `psi` a.e. measurable on this restricted raw patch can then be
applied to both sides:

```text
Measure.map psi rawOrderReferenceImage
  = Measure.map psi (rawHaar.restrict (Phi '' Omega)).
```

## Boundary

The theorem assumes the endpoint Haar-patch identification.  It does not prove
that identification, does not prove source-density lower bounds, and does not
replace the downstream package by itself.  It only moves an already-local
endpoint Haar patch through the named raw-order reference image.
