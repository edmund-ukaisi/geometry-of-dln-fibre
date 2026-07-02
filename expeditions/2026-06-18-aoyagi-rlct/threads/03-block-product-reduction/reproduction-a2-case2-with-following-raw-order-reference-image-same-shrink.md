# Reproduction - A2 with-following raw-order reference image same-shrink package

Date: 2026-07-02.

Status: measure-bookkeeping infrastructure reproduced and formalised.  This is
not a raw-Haar theorem and does not prove the determinant-chart change of
variables.

## Goal

For the enlarged Case 2 passive-theta source with an independent following
factor, name the raw-order image of the enlarged reference source and package
the local handoffs already supplied by the with-following source-chart bridge
on one common shrink.

Let

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple ... z,

Phi y =
  topologyTupleEdgeRawOrder y,

rawMap z = Phi (Y z),

referenceSource =
  case2PassiveThetaWithFollowingFactorReferenceSourceMeasure ...
```

and let

```text
rawOrderReferenceImage =
  Measure.map rawMap (referenceSource.restrict V).
```

The package should expose the useful consequences for this actual image
measure, without identifying it with raw Haar or determinant-chart Haar.

## Calculation

The existing with-following source-chart bridge gives one open set `V` around
the base point, contained in the prescribed open set `G`, such that for every
`z in V`:

```text
Y z is in the determinant chart,
rawMap z is in the raw-order source-recursive determinant chart,
rawChart (rawMap z) = sourceChart z,
readback (sourceChart z) = z.
```

The same bridge also gives the two-stage map equality for every source
measure:

```text
Measure.map rawChart (Measure.map rawMap (sourceMeasure.restrict V))
  =
Measure.map sourceChart (sourceMeasure.restrict V).
```

### Support on the raw-order source set

Since `rawMap z` lies in the raw-order source-recursive determinant chart for
all `z in V`, the restricted reference source is almost everywhere mapped into
that set.  Therefore

```text
rawOrderReferenceImage.restrict rawSourceSet = rawOrderReferenceImage.
```

### Domination

If an enlarged source measure satisfies

```text
sourceMeasure <= d * referenceSource,
```

then restriction to `V` preserves the inequality:

```text
sourceMeasure.restrict V <= d * referenceSource.restrict V.
```

The raw map is a.e. measurable on `referenceSource.restrict V`, because it is
continuous on `V`: `Y` is continuous, and `Phi` is continuous on the determinant
chart containing `Y V`.  Pushing the restricted inequality through `rawMap`
gives

```text
Measure.map rawMap (sourceMeasure.restrict V)
  <= d * rawOrderReferenceImage.
```

This is deliberately a full enlarged-source domination statement.  It does not
forget the independent following-factor coordinate.

### Endpoint image to raw image

The endpoint reference image is

```text
endpointReferenceImage = Measure.map Y (referenceSource.restrict V).
```

On the determinant chart, `Phi` is a.e. measurable, so map composition gives

```text
Measure.map Phi endpointReferenceImage
  =
Measure.map (Phi o Y) (referenceSource.restrict V)
  =
rawOrderReferenceImage.
```

### Raw chart to source chart

Taking `sourceMeasure = referenceSource` in the two-stage bridge gives

```text
Measure.map rawChart rawOrderReferenceImage
  =
Measure.map sourceChart (referenceSource.restrict V).
```

### Density handoff

For any a.e. measurable raw density on `rawOrderReferenceImage`, the generic
with-density handoff moves density through the raw-map/source-chart two-stage
identity:

```text
Measure.map rawChart (rawOrderReferenceImage.withDensity rawDensity)
  =
Measure.map sourceChart
  ((referenceSource.withDensity
    (fun theta => rawDensity (rawMap theta))).restrict V).
```

## Lean Translation

Lean now defines:

```text
case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure
```

and proves:

```text
exists_open_subset_case2PassiveThetaWithFollowingFactorRawOrderReferenceImage_same_shrink_package
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawOrderReference.lean
```

The proof uses the single shrink from
`exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse`.

## Boundary

This step names and packages an actual raw-order image of the enlarged
reference source.  It does not identify that image with raw Haar,
determinant-chart Haar, original edge-volume, or an original/source prior.  It
does not prove a Jacobian determinant formula, determinant-chart change of
variables, source-image coverage, formal-product domination, normal crossings,
pole order, or RLCT extraction.
