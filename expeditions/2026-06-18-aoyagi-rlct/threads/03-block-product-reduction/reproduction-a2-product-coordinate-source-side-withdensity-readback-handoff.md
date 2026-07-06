# A2 product-coordinate source-side withDensity readback handoff

Date: 2026-07-06

Status: pen-and-paper reproduction for the next Lean brick.

## Claim

Let `CedgeProd` be the reduced p.13 fixed-base product-coordinate map, and let
`productReadback` be the explicit readback

```text
productReadback(E) = (baseReadback(residual(E)), regularReadback(E)).
```

On the shrunken product-coordinate domain

```text
domain = source x ball(0,R),
```

the previous chart package gives:

```text
ContinuousOn CedgeProd domain
Set.InjOn CedgeProd domain
MeasurableSet (CedgeProd '' domain)
productReadback(CedgeProd z) = z        for z in domain
CedgeProd(productReadback E) = E        for E in CedgeProd '' domain.
```

Now suppose an external edge-family measure is supplied in source-side
weighted form:

```text
externalMeasure.restrict chartPiece =
  (Measure.map CedgeProd
    ((thetaReference.withDensity
      (fun z => density(CedgeProd z))).restrict domain)).restrict
    chartPiece.
```

Assume also:

```text
MeasurableSet chartPiece
AEMeasurable density (Measure.map CedgeProd (thetaReference.restrict domain))
density(E) <= c
```

almost everywhere for

```text
(Measure.map CedgeProd (thetaReference.restrict domain)).restrict chartPiece.
```

Then the generic source-side `withDensity` readback bridge gives:

```text
AEMeasurable productReadback (externalMeasure.restrict chartPiece)

Measure.map productReadback (externalMeasure.restrict chartPiece) <=
  c • thetaReference.restrict domain.
```

## Source-domain bound variant

The same conclusion follows from the pointwise source-domain bound

```text
density(CedgeProd z) <= c        for z in domain.
```

Indeed, the product-coordinate chart package gives

```text
CedgeProd(productReadback E) = E
```

for `E in CedgeProd '' domain`.  The image measure

```text
Measure.map CedgeProd (thetaReference.restrict domain)
```

is supported on `CedgeProd '' domain`, because `CedgeProd` is
a.e.-measurable on `thetaReference.restrict domain` and the image is
measurable.  Thus for almost every `E` in the restricted image measure,
`E = CedgeProd(productReadback E)` with `productReadback E in domain`, so
the pointwise source-domain bound gives

```text
density(E) <= c.
```

This is a bookkeeping upgrade, not a measure-transport theorem.  It lets
future local continuity/shrink arguments supply a pointwise bound on
`density(CedgeProd z)` over the source/product domain, rather than separately
proving the corresponding image-side a.e. bound.

## Calculation

The only measure-theoretic step is the already-proved generic bridge.  It
converts the source-side weighted identity to

```text
externalMeasure.restrict chartPiece =
  ((Measure.map CedgeProd (thetaReference.restrict domain)).withDensity
    density).restrict chartPiece,
```

then applies bounded-density readback domination using:

```text
productReadback(CedgeProd z) = z
```

on `domain`, plus `ContinuousOn` and `Set.InjOn` for `CedgeProd` on `domain`.

The new theorem should not prove a density identity.  It packages the chart
facts and says that, once the weighted identity and bound are supplied, the
readback domination follows for the actual p.13 product-coordinate map.

## Boundary

This is still not source/prior measure transport.  It does not prove the
source-side weighted identity, the a.e. density bound, determinant/raw Haar
transport, original-prior transport, normal crossings, pole order, or RLCT.
Those remain explicit future inputs.
