# Reproduction - A2 with-following endpoint selected-entry source density

Date: 2026-07-02.

Status: source-side measure convention reproduced before Lean.

## Goal

For the enlarged Case 2 passive-theta source with independent following
factor, separate two source measures:

```text
unweightedSource =
  (passiveFieldReferenceMeasure × centerSignedBoxMeasure) × followingReference
```

and the existing reference source

```text
referenceSource =
  (passiveFieldReferenceMeasure × centerWeightedBoxMeasure) × followingReference.
```

The source-density theorem should prove that `referenceSource` is obtained by
adding the selected-entry Jacobian density to `unweightedSource`, and therefore
that pushing the weighted unweighted source through the endpoint topology-tuple
map gives exactly the named endpoint reference image.

## Calculation

Let

```text
pivotNext = case2PassiveThetaPivotNext n hS hnext
densityCenter(y) =
  ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y).
```

By definition, the center weighted box is

```text
centerWeightedBox =
  centerSignedBox.withDensity densityCenter.
```

The passive-theta source is a product of passive fields and center variables.
Mathlib's product density formula gives

```text
passiveRef × centerWeightedBox
  =
(passiveRef × centerSignedBox).withDensity
  (fun theta => densityCenter theta.yNext).
```

Adding the independent following-factor coordinate is another product.  The
same product density formula gives

```text
(passiveRef × centerWeightedBox) × followingRef
  =
((passiveRef × centerSignedBox) × followingRef).withDensity
  (fun z => densityCenter z.theta.yNext).
```

The right-hand side is exactly

```text
unweightedSource.withDensity
  case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity.
```

Thus

```text
referenceSource =
  unweightedSource.withDensity selectedEntrySourceDensity.
```

Now let

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple ... z.
```

The named endpoint reference image is, by definition,

```text
endpointReferenceImage = Measure.map Y (referenceSource.restrict Omega).
```

Substituting the source-measure identity gives the source-side selected-entry
change-of-variables convention:

```text
Measure.map Y
  ((unweightedSource.withDensity selectedEntrySourceDensity).restrict Omega)
  =
endpointReferenceImage.
```

## Boundary

This is a source-side selected-entry density convention for the endpoint image.
It does not identify the endpoint image with determinant-chart Haar, does not
prove a bare `Y` determinant theorem on target Haar, and does not include the
retained-passive raw-order determinant factor.  The raw-order determinant
enters only after composing `Y` with `topologyTupleEdgeRawOrder`.

No source-image coverage, source-prior transport, raw Haar theorem,
normal-crossing theorem, pole order, or RLCT extraction is claimed.

## Kill Conditions

- If `referenceSource` is already unweighted, the theorem would double-count
  the selected-entry density.  It is not: the center factor is explicitly
  `centerSignedBox.withDensity sourceDensity`.
- If the following factor were transformed by the selected-entry chart, the
  product-density formula would need another factor.  It is independent here.
- If the conclusion were stated against determinant-chart Haar rather than the
  named endpoint reference image, it would overclaim.  The target is the actual
  image measure already defined in the endpoint-reference file.
